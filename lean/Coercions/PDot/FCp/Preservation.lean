import Coercions.PDot.FCp.CanonicalExamples

/-!
# Preservation (plan X, X5 g1)

Every step of the machine `Step appView` takes a typed state to a typed state.  The result type is
renamed along the step: by `Rename.succ` at `MS-LetVal`, which allocates, and by `Rename.id` at the
other eight rules (`preservation'`).  Along a run the renamings compose (`Steps.typed`).

The four shuffles read the inversions of `TM-Let`, `TM-Cast`, `TM-Val`, `TM-Path` and of the two
frame rules, each through its equation form.  `MS-LetPath` is the substitution of the binder by the
path evidence (`Tm.HasType.substCo`).  `MS-LetVal` splits the value into its core and its composite
cast (`Value.HasType.core_split`).  The core extends the store by `ST-Lam` or `ST-Obj`
(`Store.Typed.alloc`), and the body reads its binder as the core cast by the composite
(`Tm.HasType.adjust`, by `CoSubst.Typed.selfCast` and `Ctx.Refines`).  The three application rules
are `app_preservation` of `CanonicalForms`.

The examples are in `namespace PDot.FCp.X5Ex` and restate the acceptance of the stage.  N3's state
steps by `MS-AppEq` to a typed state (`X5Ex.N3.step_typed`, over `C0Ex.R2`).  R3's program binds a
nested literal by a `let` over its path and runs with the store unchanged (`X5Ex.R3.run`).  G6's
program binds a path cast to `⊤` by a `let` whose binder is opaque at `⊤`, and the state after
`MS-LetPath` is typed (`X5Ex.G6.st₂_typed`).  A cast literal is allocated under a body whose
`PA-Alias` has the binder as its first premise, and the state after `MS-LetVal` is typed
(`X5Ex.LetVal.step_typed`).
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Inversions of term and frame typing -/

theorem Tm.HasType.path_inv_of_eq : ∀ {Γ : Ctx s} {t : Tm s} {T : Ty s}, Tm.HasType Γ t T →
    ∀ (P : PathCo s), t = .path P → PathCo.HasType Γ P T
  | _, _, _, .path h, _, e => by cases e; exact h
  | _, _, _, .val _, _, e => nomatch e
  | _, _, _, .app _ _, _, e => nomatch e
  | _, _, _, .lett _ _, _, e => nomatch e
  | _, _, _, .cast _ _, _, e => nomatch e

theorem Tm.HasType.path_inv {Γ : Ctx s} {P : PathCo s} {T : Ty s} (h : Tm.HasType Γ (.path P) T) :
    PathCo.HasType Γ P T :=
  h.path_inv_of_eq P rfl

theorem Tm.HasType.val_inv_of_eq : ∀ {Γ : Ctx s} {t : Tm s} {T : Ty s}, Tm.HasType Γ t T →
    ∀ (v : Value s), t = .val v → Value.HasType Γ v T
  | _, _, _, .val h, _, e => by cases e; exact h
  | _, _, _, .path _, _, e => nomatch e
  | _, _, _, .app _ _, _, e => nomatch e
  | _, _, _, .lett _ _, _, e => nomatch e
  | _, _, _, .cast _ _, _, e => nomatch e

theorem Tm.HasType.val_inv {Γ : Ctx s} {v : Value s} {T : Ty s} (h : Tm.HasType Γ (.val v) T) :
    Value.HasType Γ v T :=
  h.val_inv_of_eq v rfl

theorem Tm.HasType.lett_inv_of_eq : ∀ {Γ : Ctx s} {t' : Tm s} {U : Ty s}, Tm.HasType Γ t' U →
    ∀ (t : Tm s) (u : Tm (s,x)), t' = .lett t u →
      ∃ T, Tm.HasType Γ t T ∧ Tm.HasType (Γ.cons (.opaque T)) u U.weaken
  | _, _, _, .lett ht hu, _, _, e => by cases e; exact ⟨_, ht, hu⟩
  | _, _, _, .path _, _, _, e => nomatch e
  | _, _, _, .val _, _, _, e => nomatch e
  | _, _, _, .app _ _, _, _, e => nomatch e
  | _, _, _, .cast _ _, _, _, e => nomatch e

theorem Tm.HasType.lett_inv {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} {U : Ty s} (h : Tm.HasType Γ (.lett t u) U) :
    ∃ T, Tm.HasType Γ t T ∧ Tm.HasType (Γ.cons (.opaque T)) u U.weaken :=
  h.lett_inv_of_eq t u rfl

theorem Tm.HasType.cast_inv_of_eq : ∀ {Γ : Ctx s} {t' : Tm s} {T : Ty s}, Tm.HasType Γ t' T →
    ∀ (t : Tm s) (e : LeCo s), t' = .cast t e → ∃ S, Tm.HasType Γ t S ∧ LeCo.HasType Γ e S T
  | _, _, _, .cast ht he, _, _, h => by cases h; exact ⟨_, ht, he⟩
  | _, _, _, .path _, _, _, h => nomatch h
  | _, _, _, .val _, _, _, h => nomatch h
  | _, _, _, .app _ _, _, _, h => nomatch h
  | _, _, _, .lett _ _, _, _, h => nomatch h

theorem Tm.HasType.cast_inv {Γ : Ctx s} {t : Tm s} {e : LeCo s} {T : Ty s} (h : Tm.HasType Γ (.cast t e) T) :
    ∃ S, Tm.HasType Γ t S ∧ LeCo.HasType Γ e S T :=
  h.cast_inv_of_eq t e rfl

theorem Cont.Typed.lett_inv_of_eq : ∀ {Γ : Ctx s} {K' : Cont s} {T V : Ty s}, Cont.Typed Γ K' T V →
    ∀ (K : Cont s) (u : Tm (s,x)), K' = .cons K (.lett u) →
      ∃ U, Tm.HasType (Γ.cons (.opaque T)) u U.weaken ∧ Cont.Typed Γ K U V
  | _, _, _, _, .lett hu hK, _, _, e => by cases e; exact ⟨_, hu, hK⟩
  | _, _, _, _, .nil, _, _, e => nomatch e
  | _, _, _, _, .cast _ _, _, _, e => nomatch e

theorem Cont.Typed.lett_inv {Γ : Ctx s} {K : Cont s} {u : Tm (s,x)} {T V : Ty s}
    (h : Cont.Typed Γ (.cons K (.lett u)) T V) :
    ∃ U, Tm.HasType (Γ.cons (.opaque T)) u U.weaken ∧ Cont.Typed Γ K U V :=
  h.lett_inv_of_eq K u rfl

theorem Cont.Typed.cast_inv_of_eq : ∀ {Γ : Ctx s} {K' : Cont s} {T V : Ty s}, Cont.Typed Γ K' T V →
    ∀ (K : Cont s) (e : LeCo s), K' = .cons K (.cast e) → ∃ U, LeCo.HasType Γ e T U ∧ Cont.Typed Γ K U V
  | _, _, _, _, .cast he hK, _, _, h => by cases h; exact ⟨_, he, hK⟩
  | _, _, _, _, .nil, _, _, h => nomatch h
  | _, _, _, _, .lett _ _, _, _, h => nomatch h

theorem Cont.Typed.cast_inv {Γ : Ctx s} {K : Cont s} {e : LeCo s} {T V : Ty s}
    (h : Cont.Typed Γ (.cons K (.cast e)) T V) : ∃ U, LeCo.HasType Γ e T U ∧ Cont.Typed Γ K U V :=
  h.cast_inv_of_eq K e rfl

/-! ## The allocation of `MS-LetVal` -/

/-- A typed value is its core, typed at some `S`, cast by its composite from `S` to the value's type.
With no composite the two types are one. -/
theorem Value.HasType.core_split : ∀ {Γ : Ctx s} (v : Value s) {T : Ty s}, Value.HasType Γ v T →
    ∃ S, Value.HasType Γ v.core S ∧
      ((v.composite = none ∧ S = T) ∨ ∃ E, v.composite = some E ∧ LeCo.HasType Γ E S T)
  | _, .lam _ _, _, h => ⟨_, h, .inl ⟨rfl, rfl⟩⟩
  | _, .obj _ _, _, h => ⟨_, h, .inl ⟨rfl, rfl⟩⟩
  | _, .cast v e, _, h => by
      obtain ⟨S', hv, he⟩ := h.cast_inv_of_eq v e rfl
      obtain ⟨S, hc, hcomp⟩ := Value.HasType.core_split v hv
      refine ⟨S, hc, .inr ?_⟩
      rcases hcomp with ⟨hn, rfl⟩ | ⟨E, hE, hES⟩
      · exact ⟨e, by simp only [Value.composite, hn], he⟩
      · exact ⟨.trans E e, by simp only [Value.composite, hE], .trans hES he⟩

/-- The core of a value is a lambda or a literal. -/
theorem Value.core_shape : ∀ (v : Value s), (∃ S t, v.core = .lam S t) ∨ (∃ Tel ds, v.core = .obj Tel ds)
  | .lam _ _ => .inl ⟨_, _, rfl⟩
  | .obj _ _ => .inr ⟨_, _, rfl⟩
  | .cast v _ => Value.core_shape v

/-- `MS-LetVal` extends a typed store by the core of a value: a lambda opaque at its type by
`ST-Lam`, a literal transparent at its type with its block by `ST-Obj`.  The new binding refines
an opaque binding at the core's type. -/
theorem Store.Typed.alloc {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {v : Value s} {S : Ty s}
    (hv : Value.HasType Γ v.core S) :
    ∃ b : Binding s, b.ty = S ∧ (Γ.cons (.opaque S)).Refines (Γ.cons b) ∧ Store.Typed (σ.cons v.core) (Γ.cons b) := by
  rcases Value.core_shape v with ⟨S₀, t, e⟩ | ⟨Tel, ds, e⟩
  · rw [e] at hv ⊢
    obtain ⟨T, rfl, _⟩ := hv.lam_inv_of_eq S₀ t rfl
    exact ⟨.opaque (.pi S₀ T), rfl, Ctx.Refines.refl _, .lam hσ hv⟩
  · rw [e] at hv ⊢
    obtain ⟨rfl, _⟩ := hv.obj_inv
    exact ⟨.transparent (.mu Tel) ds.block, rfl, Ctx.Refines.here _ _ _, .obj hσ hv⟩

/-- The body of `MS-LetVal` after the allocation.  It was typed at an opaque binder of the value's
type `T`.  The new binder has the core's type `S`, and the body reads it cast by the composite. -/
theorem Tm.HasType.adjust {Γ : Ctx s} {v : Value s} {S T : Ty s} {b : Binding s} {u : Tm (s,x)} {U : Ty (s,x)}
    (hu : Tm.HasType (Γ.cons (.opaque T)) u U)
    (hc : (v.composite = none ∧ S = T) ∨ ∃ E, v.composite = some E ∧ LeCo.HasType Γ E S T)
    (hb : b.ty = S) (hr : (Γ.cons (.opaque S)).Refines (Γ.cons b)) :
    Tm.HasType (Γ.cons b) (u.adjust v) U := by
  rcases hc with ⟨hn, rfl⟩ | ⟨E, hE, hES⟩
  · have e : u.adjust v = u := by unfold Tm.adjust; rw [hn]
    rw [e]
    exact hu.refines hr
  · have e : u.adjust v = u.subst (CoSubst.selfCast E) := by unfold Tm.adjust; rw [hE]
    rw [e]
    have h := Tm.HasType.subst (CoSubst.Typed.selfCast hES b hb) hu
    rwa [CoSubst.selfCast_paths, Ty.subst_ofRename, Ty.rename_id] at h

/-! ## The steps that read no view -/

/-- `MS-Let`. -/
theorem lett_preservation {σ : Store s} {K : Cont s} {t : Tm s} {u : Tm (s,x)} {U : Ty s}
    (hst : State.Typed ⟨σ, K, .lett t u⟩ U) : State.Typed ⟨σ, .cons K (.lett u), t⟩ U := by
  obtain ⟨Γ, T', hσ, ht, hK⟩ := hst
  obtain ⟨T, ht₀, hu⟩ := Tm.HasType.lett_inv ht
  exact ⟨Γ, T, hσ, ht₀, .lett hu hK⟩

/-- `MS-CastPush`. -/
theorem castPush_preservation {σ : Store s} {K : Cont s} {t : Tm s} {e : LeCo s} {U : Ty s}
    (hst : State.Typed ⟨σ, K, .cast t e⟩ U) : State.Typed ⟨σ, .cons K (.cast e), t⟩ U := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := hst
  obtain ⟨S, ht₀, he⟩ := Tm.HasType.cast_inv ht
  exact ⟨Γ, S, hσ, ht₀, .cast he hK⟩

/-- `MS-CastVal`. -/
theorem castVal_preservation {σ : Store s} {K : Cont s} {e : LeCo s} {v : Value s} {U : Ty s}
    (hst : State.Typed ⟨σ, .cons K (.cast e), .val v⟩ U) : State.Typed ⟨σ, K, .val (.cast v e)⟩ U := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := hst
  obtain ⟨T', he, hK'⟩ := Cont.Typed.cast_inv hK
  exact ⟨Γ, T', hσ, .val (.cast (Tm.HasType.val_inv ht) he), hK'⟩

/-- `MS-CastPath`. -/
theorem castPath_preservation {σ : Store s} {K : Cont s} {e : LeCo s} {P : PathCo s} {U : Ty s}
    (hst : State.Typed ⟨σ, .cons K (.cast e), .path P⟩ U) : State.Typed ⟨σ, K, .path (.cast P e)⟩ U := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := hst
  obtain ⟨T', he, hK'⟩ := Cont.Typed.cast_inv hK
  exact ⟨Γ, T', hσ, .path (.cast (Tm.HasType.path_inv ht) he), hK'⟩

/-- `MS-LetVal`.  The store grows by one variable and the result type is weakened. -/
theorem letVal_preservation {σ : Store s} {K : Cont s} {u : Tm (s,x)} {v : Value s} {U : Ty s}
    (hst : State.Typed ⟨σ, .cons K (.lett u), .val v⟩ U) :
    State.Typed ⟨σ.cons v.core, K.weaken, u.adjust v⟩ U.weaken := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := hst
  obtain ⟨S, hcore, hc⟩ := Value.HasType.core_split v (Tm.HasType.val_inv ht)
  obtain ⟨U', hu, hK'⟩ := Cont.Typed.lett_inv hK
  obtain ⟨b, hb, hr, hσ'⟩ := hσ.alloc hcore
  exact ⟨Γ.cons b, U'.weaken, hσ', Tm.HasType.adjust hu hc hb hr, Cont.Typed.rename (Rename.Typed.succ Γ b) hK'⟩

/-- `MS-LetPath`.  The binder is replaced by the path evidence, and the store is unchanged. -/
theorem letPath_preservation {σ : Store s} {K : Cont s} {u : Tm (s,x)} {P : PathCo s} {U : Ty s}
    (hst : State.Typed ⟨σ, .cons K (.lett u), .path P⟩ U) : State.Typed ⟨σ, K, u.substCo P⟩ U := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := hst
  obtain ⟨U', hu, hK'⟩ := Cont.Typed.lett_inv hK
  have h := Tm.HasType.substCo (Tm.HasType.path_inv ht) hu
  rw [Ty.weaken_substPath] at h
  exact ⟨Γ, U', hσ, h, hK'⟩

/-! ## Preservation at the nine rules -/

/-- `preservation'` (`plan-10-pdot.md:873`): a step of the machine at `appView` takes a typed state
to a state typed at the renamed result type. -/
theorem preservation' {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hst : st.Typed U) (hs : Step appView st st') : ∃ ρ : Rename s s', st'.Typed (U.rename ρ) := by
  cases hs with
  | lett => exact ⟨Rename.id, by rw [Ty.rename_id]; exact lett_preservation hst⟩
  | castPush => exact ⟨Rename.id, by rw [Ty.rename_id]; exact castPush_preservation hst⟩
  | castVal => exact ⟨Rename.id, by rw [Ty.rename_id]; exact castVal_preservation hst⟩
  | castPath => exact ⟨Rename.id, by rw [Ty.rename_id]; exact castPath_preservation hst⟩
  | letVal => exact ⟨Rename.succ, letVal_preservation hst⟩
  | letPath => exact ⟨Rename.id, by rw [Ty.rename_id]; exact letPath_preservation hst⟩
  | appId hv => exact ⟨Rename.id, by rw [Ty.rename_id]; exact app_preservation hst (.appId hv)⟩
  | appPi hv => exact ⟨Rename.id, by rw [Ty.rename_id]; exact app_preservation hst (.appPi hv)⟩
  | appEq hv => exact ⟨Rename.id, by rw [Ty.rename_id]; exact app_preservation hst (.appEq hv)⟩

/-- Along a run of the machine the state stays typed, at the result type renamed by the composite
of the steps' renamings. -/
theorem Steps.typed {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hst : st.Typed U) (run : Steps appView st st') : ∃ ρ : Rename s s', st'.Typed (U.rename ρ) := by
  induction run with
  | refl => exact ⟨Rename.id, by rw [Ty.rename_id]; exact hst⟩
  | tail _ step ih =>
      obtain ⟨ρ, h⟩ := ih hst
      obtain ⟨ρ', h'⟩ := preservation' h step
      rw [Ty.rename_rename] at h'
      exact ⟨_, h'⟩

end PDot.FCp

/-! # The acceptance of g1 -/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace X5Ex

/-! ## N3: `MS-AppEq` on N3's store, by `preservation'` -/

namespace N3

/-- `C0Ex.R2.step` with `C0Ex.R2.st'_typed`, restated: N3's state steps by `MS-AppEq`, and the state
after the step is typed by `preservation'`. -/
theorem step_typed : Step appView C0Ex.R2.st C0Ex.R2.st' ∧
    ∃ ρ : Rename (([],x),x) (([],x),x), C0Ex.R2.st'.Typed (Ty.top.rename ρ) :=
  ⟨C0Ex.R2.step, preservation' C0Ex.R2.st_typed C0Ex.R2.step⟩

end N3

/-! ## R3: a `let` over the path of a nested literal copies nothing (`facts.md:1305-1312`) -/

namespace R3

abbrev ra : Label := .trm 0
abbrev rC : Label := .typ 1
abbrev rB : Label := .typ 2

/-- The nested literal's annotation, under its self `v`: `{C : ⊤..⊤} ∧ {B : v.C..v.C}`. -/
def telA : Telescope (s,x) :=                                    -- v the .here, the nested literal's self
  .cons (.cons (.cons (.cons .nil (.le .top (.sel (.var .here) rC))) (.le (.sel (.var .here) rC) .top))
    (.le (.sel (.var .here) rC) (.sel (.var .here) rB))) (.le (.sel (.var .here) rB) (.sel (.var .here) rC))
def telX : Telescope ([],x) := .cons .nil (.fld ra (.mu telA))   -- w the .here, x's self, v of telA
/-- `{C = ⊤} ∧ {B = x.a.C}`, the nested literal's self named by its path `x.a`. -/
def dsA : Defs ([],x) := .typ (.typ .nil rC .top) rB (.sel ((Path.var .here).sel ra) rC)   -- .here is x
/-- `ν(x. {a = ν(z. {C = ⊤} ∧ {B = z.C})})`. -/
def dsX : Defs ([],x) := .fld .nil ra (.nest telA dsA)          -- .here is x, v of telA
def Γ : Ctx ([],x) := Ctx.nil.cons (.transparent (.mu telX) dsX.block)
def σ : Store ([],x) := Store.nil.cons (.obj telX dsX)
theorem σ_typed : Store.Typed σ Γ := .obj .nil (synthValue_sound (by decide +kernel))

/-- `x.a`. -/
def Pxa : PathCo ([],x) := .sel (.var .here) ra 0
/-- `let y = x.a in y`. -/
def t : Tm ([],x) := .lett (.path Pxa) (.path (.var .here))     -- y the .here of the body
def st : State ([],x) := ⟨σ, .nil, t⟩
def st₂ : State ([],x) := ⟨σ, .nil, .path Pxa⟩

theorem st_typed : st.Typed (.mu telA) :=
  ⟨Γ, _, σ_typed, synthTm_sound (by decide +kernel), .nil⟩

/-- The run: `MS-Let`, then `MS-LetPath`. -/
theorem run : Steps appView st st₂ := .tail (.tail .refl .lett) .letPath

/-- The store after the run is the store before it: no step copies the nested literal. -/
theorem store_unchanged : st₂.σ = st.σ := rfl

theorem st₂_final : st₂.Final := ⟨rfl, .inr ⟨Pxa, rfl⟩⟩

theorem st₂_typed : ∃ ρ : Rename ([],x) ([],x), st₂.Typed ((Ty.mu telA).rename ρ) :=
  Steps.typed st_typed run

/-- `x.a∙B` unfolds at the one location `x.a`. -/
theorem defAt_xaB : Γ.defAt ((Path.var .here).sel ra) rB = some (.sel ((Path.var .here).sel ra) rC) := by
  decide +kernel

end R3

/-! ## G6: a `let` over a cast path has an opaque binder (`facts.md:1287-1295`) -/

namespace G6

abbrev lA : Label := .typ 0

/-- `x`'s annotation, under its self: `{A : ⊥..⊥}`. -/
def telX : Telescope ([],x) :=                                    -- z the .here, x's self
  .cons (.cons .nil (.le .bot (.sel (.var .here) lA))) (.le (.sel (.var .here) lA) .bot)
def dsX : Defs ([],x) := .typ .nil lA .bot                       -- .here is x
/-- `y`'s annotation, under its self: `{A : ⊤..⊤}`. -/
def telY : Telescope (([],x),x) :=                                -- z the .here, y's self
  .cons (.cons .nil (.le .top (.sel (.var .here) lA))) (.le (.sel (.var .here) lA) .top)
def dsY : Defs (([],x),x) := .typ .nil lA .top                   -- .here is y
/-- `x : μ(z. {A : ⊥..⊥})`, then `y : μ(z. {A : ⊤..⊤})`. -/
def Γ : Ctx (([],x),x) := (Ctx.nil.cons (.transparent (.mu telX) dsX.block)).cons (.transparent (.mu telY) dsY.block)
/-- `ν(z. {A = ⊥})` at `x` and `ν(z. {A = ⊤})` at `y`. -/
def σ : Store (([],x),x) := (Store.nil.cons (.obj telX dsX)).cons (.obj telY dsY)
theorem σ_typed : Store.Typed σ Γ :=
  .obj (.obj .nil (synthValue_sound (by decide +kernel))) (synthValue_sound (by decide +kernel))

/-- `aTop`: `y` cast to `⊤`. -/
def aTop : PathCo (([],x),x) := .cast (.var .here) (.top (Γ.ty .here))   -- .here is y
/-- `let z = aTop in z`. -/
def t : Tm (([],x),x) := .lett (.path aTop) (.path (.var .here))   -- z the .here of the body
def st : State (([],x),x) := ⟨σ, .nil, t⟩
def st₂ : State (([],x),x) := ⟨σ, .nil, .path aTop⟩

/-- The binder of `TM-Let` is opaque at `⊤`, the type of `aTop`. -/
theorem st_typed : st.Typed .top := ⟨Γ, .top, σ_typed, synthTm_sound (by decide +kernel), .nil⟩

/-- The run: `MS-Let`, then `MS-LetPath`. -/
theorem run : Steps appView st st₂ := .tail (.tail .refl .lett) .letPath

theorem st₂_final : st₂.Final := ⟨rfl, .inr ⟨aTop, rfl⟩⟩

/-- The state after the substitution of `aTop` is typed. -/
theorem st₂_typed : ∃ ρ : Rename (([],x),x) (([],x),x), st₂.Typed (Ty.top.rename ρ) :=
  Steps.typed st_typed run

/-- The two literals keep their own blocks: `x∙A` reads `⊥` and `y∙A` reads `⊤`. -/
theorem blocks_differ :                                           -- .there .here is x, .here is y
    Γ.defAt (.var (.there .here)) lA = some .bot ∧ Γ.defAt (.var .here) lA = some .top := by
  decide +kernel

end G6

/-! ## `MS-LetVal` with a composite cast (the risk of X2 g3, `Examples.lean`, `Adjust`) -/

namespace LetVal

theorem lit_typed : Value.HasType .nil PDot.FCp.Adjust.lit (.mu PDot.FCp.Adjust.tel) :=
  synthValue_sound (by decide +kernel)

/-- `⟨[], [▹ let z. body], val (cast lit E)⟩`. -/
def st : State [] :=                                                -- z the .here of the body
  ⟨.nil, .cons .nil (.lett PDot.FCp.Adjust.body), .val (.cast PDot.FCp.Adjust.lit PDot.FCp.Adjust.E)⟩
/-- The state after `MS-LetVal`: the core `lit` is stored, the body reads its binder cast by `E`. -/
def st' : State ([],x) :=                                           -- the new store variable is z
  ⟨Store.nil.cons PDot.FCp.Adjust.lit, Cont.nil.weaken, PDot.FCp.Adjust.body.adjust (.cast PDot.FCp.Adjust.lit PDot.FCp.Adjust.E)⟩

theorem st_typed : st.Typed .top :=
  ⟨.nil, .top, .nil, .val (.cast lit_typed .top), .lett (U := .top) PDot.FCp.Adjust.body_typed .nil⟩

theorem step : Step appView st st' := .letVal

theorem step_typed : ∃ ρ : Rename [] ([],x), st'.Typed (Ty.top.rename ρ) := preservation' st_typed step

end LetVal

end X5Ex

end PDot.FCp
