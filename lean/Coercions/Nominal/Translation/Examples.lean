import Coercions.Nominal.Translation.Safety

/-!
# The examples at both levels (plan X, stage X7, group g2)

The mandatory examples of plan X (`plan-10-pdot.md:972-996`) on the source and on FCn.

* Two evaluators, each structural on its term with fuel for its loops, so a run by
  `decide +kernel` proves a reduction sequence.  `Source.runFuel` runs the source, as
  `PDot.Runtime.runFuel` runs the runtime, with `Source.Reds.of_runFuel`.  `Translation.runOf` runs the
  FCn machine at `appView`, which `FCn.appViewOf` computes, with `Translation.steps_of_runOf`.
  `Translation.finalB` decides a final state.  The runs of E5, E7 and E8 are in `Pages`.
* E1 to E11 and E13.  The FCn checker accepts the image of each derivation of X0 at the
  translated type, by `decide +kernel` on `checkTm` or `checkPath` (`E1_checks` to `E11_checks`
  and `E13_checks`).  The kernel runs the translation of the whole derivation.  E9 to E11 are path
  typings in a context, checked in the translated context.  E11 is checked at `T = ⊤`.
* E12 has no derivation.  It is a lookup on a store.  The lookup of `x.a.c` reaches `λ(z : ⊤) z`
  in the source, on the erased store, and on the erasure of X3's typed FCn store
  (`FCn.C0Ex.E12.σ`), which is the erased source store (`E12_three`).
* N1 to N3.  The source has no derivation of the literal (X0).  The image a derivation would build
  is `obj (z : tel T) ds`, with `T` the literal's annotation and `ds` the image of its definitions.
  No such FCn value is typed, whatever the evidence in `ds` (`N1_image_untyped` to
  `N3_image_untyped`), and with the evidence at the source's paths it erases to the source literal
  (`N1_image_erase` to `N3_image_erase`).  N3's proof reads the metatheory: the literal's store
  would be typed, so its field's path would have a safe lookup (`path_safe`), and the lookup of
  `x.zz` is stuck.
* N4.  The source has no derivation of `x : x.type` (X0).  FCn types `x` at `x.type` by `PA-Sngl`
  over `PE-Refl` (`N4_target_refl`).  The target is looser here, as decision 21 of the plan says
  (`plan-10-pdot.md:1252-1255`), and every theorem of the target holds of that term too.
* N5.  The third premise of `ty_def_new` holds where `tight_bounds` fails (X0), and the image of
  its definitions is typed against the opened annotation and not against the annotation that is not
  tight (X6).  `N5_both` states the two levels together.

Binders are named in comments only.  `(s,x)` adds one variable, and `.here` is the newest variable
of a signature.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The source evaluator, fuelled -/

/-- One source lookup step from `defp p`, computed.  Structural on the path. -/
def lookPath (γ : Store s) : Path s → Option (Rhs s)
  | .var x => some (.defv (γ.get x))                              -- lookup_var
  | .sel p a =>
      match lookPath γ p with
      | some (.defp q) => some (.defp (q.sel a))                    -- lookup_sel_p
      | some (.defv (.new _ ds)) =>
          match ds.get a with
          | some (.trm _ r) => some (r.substPath p)                 -- lookup_sel_v, r under the self
          | _ => none
      | _ => none

theorem LStep.of_lookPath {γ : Store s} : ∀ {p : Path s} {r : Rhs s},
    lookPath γ p = some r → LStep γ (.defp p) r
  | .var x, r, h => by
      simp only [lookPath, Option.some.injEq] at h
      subst h
      exact .lookup_var
  | .sel p a, r, h => by
      simp only [lookPath] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq] at h
        subst h
        exact .lookup_sel_p (LStep.of_lookPath hq)
      · rename_i T ds hq
        split at h
        · rename_i b r₀ hg
          simp only [Option.some.injEq] at h
          subst h
          have hb : b = a := Defs.get_label ds hg
          subst hb
          exact .lookup_sel_v (LStep.of_lookPath hq) hg
        · cases h
      · cases h

/-- Source lookup iterated at most `n` times. -/
def lookStar (γ : Store s) : Nat → Rhs s → Rhs s
  | 0, r => r
  | n+1, .defp p =>
      match lookPath γ p with
      | some r => lookStar γ n r
      | none => .defp p
  | _+1, r => r

theorem Lookups.of_lookStar {γ : Store s} : ∀ (n : Nat) (r : Rhs s), Lookups γ r (lookStar γ n r)
  | 0, _ => .refl
  | n+1, .defp p => by
      simp only [lookStar]
      split
      · rename_i r hr
        exact .step (LStep.of_lookPath hr) (Lookups.of_lookStar n r)
      · exact .refl
  | _+1, .defv _ => .refl

/-- One source step, computed, with the renaming of its store.  The lookup of `red_app` runs with
fuel `n`.  Structural on the term. -/
def stepFuel (n : Nat) (γ : Store s) : Tm s → Option ((s' : Sig) × Store s' × Tm s' × Rename s s')
  | .app q p =>                                                               -- red_app
      match lookStar γ n (.defp q) with
      | .defv (.lam _ t) => some ⟨s, γ, t.substPath p, Rename.id⟩
      | _ => none
  | .lett (.val v) t => some ⟨(s,x), γ.cons v, t, Rename.succ⟩               -- red_let_val
  | .lett (.path p) t => some ⟨s, γ, t.substPath p, Rename.id⟩               -- red_let_path
  | .lett t₀ t =>                                                             -- red_let_tgt
      match stepFuel n γ t₀ with
      | some ⟨s', γ', t₀', ρ⟩ => some ⟨s', γ', .lett t₀' (t.rename ρ.lift), ρ⟩
      | none => none
  | _ => none

theorem Red.of_stepFuel {n : Nat} : ∀ {s : Sig} {γ : Store s} {t : Tm s} {s' : Sig}
    {γ' : Store s'} {t' : Tm s'} {ρ : Rename s s'},
    stepFuel n γ t = some ⟨s', γ', t', ρ⟩ → Red ⟨s, γ, t⟩ ⟨s', γ', t'⟩ ρ
  | s, γ, .app q p, s', γ', t', ρ, h => by
      simp only [stepFuel] at h
      split at h
      · rename_i T t hl
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have := Lookups.of_lookStar (γ := γ) n (.defp q)
        rw [hl] at this
        exact .red_app this
      · cases h
  | s, γ, .lett (.val v) t, s', γ', t', ρ, h => by
      simp only [stepFuel, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .red_let_val
  | s, γ, .lett (.path p) t, s', γ', t', ρ, h => by
      simp only [stepFuel, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .red_let_path
  | s, γ, .lett (.app q p) t, s', γ', t', ρ, h => by
      simp only [stepFuel] at h
      split at h
      · rename_i s'' γ'' t₀' ρ' h0
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .red_let_tgt (Red.of_stepFuel h0)
      · cases h
  | s, γ, .lett (.lett t₀ t₁) t, s', γ', t', ρ, h => by
      simp only [stepFuel] at h
      split at h
      · rename_i s'' γ'' t₀' ρ' h0
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .red_let_tgt (Red.of_stepFuel h0)
      · cases h
  | _, _, .path _, _, _, _, _, h => by
      simp only [stepFuel] at h
      cases h
  | _, _, .val _, _, _, _, _, h => by
      simp only [stepFuel] at h
      cases h

/-- At most `m` source steps, each with lookup fuel `n`. -/
def runFuel (n : Nat) : Nat → Conf → Conf
  | 0, c => c
  | m+1, ⟨s, γ, t⟩ =>
      match stepFuel n γ t with
      | some ⟨s', γ', t', _⟩ => runFuel n m ⟨s', γ', t'⟩
      | none => ⟨s, γ, t⟩

theorem Reds.of_runFuel (n : Nat) : ∀ (m : Nat) (c : Conf), Reds c (runFuel n m c)
  | 0, _ => .refl
  | m+1, ⟨s, γ, t⟩ => by
      simp only [runFuel]
      split
      · rename_i s' γ' t' ρ h
        exact .step ⟨ρ, Red.of_stepFuel h⟩ (Reds.of_runFuel n m _)
      · exact .refl

end Nominal.Source

namespace Nominal.Translation

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The FCn machine, fuelled -/

/-- One step of the FCn machine at `appView`, computed.  `FCn.appViewOf` computes the application
view.  Structural, by cases on the state. -/
def stepOf {s : Sig} : FCn.State s → Option ((s' : Sig) × FCn.State s')
  | ⟨σ, K, .lett t u⟩ => some ⟨s, ⟨σ, .cons K (.lett u), t⟩⟩                            -- MS-Let
  | ⟨σ, K, .cast t e⟩ => some ⟨s, ⟨σ, .cons K (.cast e), t⟩⟩                            -- MS-CastPush
  | ⟨σ, .cons K (.cast e), .val v⟩ => some ⟨s, ⟨σ, K, .val (.cast v e)⟩⟩               -- MS-CastVal
  | ⟨σ, .cons K (.cast e), .path P⟩ => some ⟨s, ⟨σ, K, .path (.cast P e)⟩⟩             -- MS-CastPath
  | ⟨σ, .cons K (.lett u), .val v⟩ => some ⟨(s,x), ⟨σ.cons v.core, K.weaken, u.adjust v⟩⟩   -- MS-LetVal
  | ⟨σ, .cons K (.lett u), .path P⟩ => some ⟨s, ⟨σ, K, u.substCo P⟩⟩                   -- MS-LetPath
  | ⟨σ, K, .app P Q⟩ =>
      match FCn.appViewOf σ P with
      | some (_, t₀, .id) => some ⟨s, ⟨σ, K, t₀.substCo Q⟩⟩                             -- MS-AppId
      | some (_, t₀, .pi d c) =>                                                         -- MS-AppPi
          some ⟨s, ⟨σ, K, .cast (t₀.substCo (.cast Q d)) (c.substCo Q)⟩⟩
      | some (_, t₀, .eqv φ) =>                                                          -- MS-AppEq
          some ⟨s, ⟨σ, K, .cast (t₀.substCo (.cast Q (.eqToLe (.symm (.dom φ))))) (.eqToLe (.cod φ Q.path))⟩⟩
      | none => none
  | _ => none

theorem step_of_stepOf {s : Sig} {st : FCn.State s} {s' : Sig} {st' : FCn.State s'}
    (h : stepOf st = some ⟨s', st'⟩) : FCn.Step FCn.appView st st' := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | lett t u =>
      simp only [stepOf, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases eq_of_heq h
      exact .lett
  | cast t e =>
      simp only [stepOf, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases eq_of_heq h
      exact .castPush
  | app P Q =>
      simp only [stepOf] at h
      split at h
      · rename_i S₀ t₀ hv
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        cases eq_of_heq h
        exact .appId (FCn.appViewOf_iff.1 hv)
      · rename_i S₀ t₀ d c hv
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        cases eq_of_heq h
        exact .appPi (FCn.appViewOf_iff.1 hv)
      · rename_i S₀ t₀ φ hv
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        cases eq_of_heq h
        exact .appEq (FCn.appViewOf_iff.1 hv)
      · cases h
  | val v =>
      cases K with
      | nil => simp [stepOf] at h
      | cons K fr =>
          cases fr with
          | lett u =>
              simp only [stepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h
              cases eq_of_heq h
              exact .letVal
          | cast e =>
              simp only [stepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h
              cases eq_of_heq h
              exact .castVal
  | path P =>
      cases K with
      | nil => simp [stepOf] at h
      | cons K fr =>
          cases fr with
          | lett u =>
              simp only [stepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h
              cases eq_of_heq h
              exact .letPath
          | cast e =>
              simp only [stepOf, Option.some.injEq, Sigma.mk.injEq] at h
              obtain ⟨rfl, h⟩ := h
              cases eq_of_heq h
              exact .castPath

/-- At most `m` steps of the machine. -/
def runOf : Nat → (s : Sig) × FCn.State s → (s : Sig) × FCn.State s
  | 0, p => p
  | m+1, ⟨s, st⟩ =>
      match stepOf st with
      | some p => runOf m p
      | none => ⟨s, st⟩

theorem steps_of_runOf : ∀ (m : Nat) (p : (s : Sig) × FCn.State s), FCn.Steps FCn.appView p.2 (runOf m p).2
  | 0, _ => .refl
  | m+1, ⟨s, st⟩ => by
      simp only [runOf]
      split
      · rename_i p h
        exact FCn.Steps.head (step_of_stepOf h) (steps_of_runOf m p)
      · exact .refl

/-- A final state, decided: no frame, and a value or a path in focus. -/
def finalB {s : Sig} : FCn.State s → Bool
  | ⟨_, .nil, .val _⟩ => true
  | ⟨_, .nil, .path _⟩ => true
  | _ => false

theorem final_of_finalB {s : Sig} {st : FCn.State s} (h : finalB st = true) : st.Final := by
  obtain ⟨σ, K, t⟩ := st
  cases K with
  | nil =>
      cases t with
      | val v => exact ⟨rfl, .inl ⟨v, rfl⟩⟩
      | path P => exact ⟨rfl, .inr ⟨P, rfl⟩⟩
      | app _ _ => simp [finalB] at h
      | lett _ _ => simp [finalB] at h
      | cast _ _ => simp [finalB] at h
  | cons _ _ => cases t <;> simp [finalB] at h

end Nominal.Translation

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## E1 to E11 and E13: the checker accepts the images -/

/-- E1, pDOT's Fig. 1. -/
theorem E1_checks : FCn.checkTm .nil E1_d.translate (Ty.mu e1_Td).translate = true := by decide +kernel
/-- E2, the length-two path. -/
theorem E2_checks : FCn.checkTm .nil E2_d.translate (Ty.mu e2_Tz).translate = true := by decide +kernel
/-- E3, `compiler_typecheck`. -/
theorem E3_checks : FCn.checkTm .nil CP_d.translate compiler_T.translate = true := by decide +kernel
/-- E4, `list_typing`. -/
theorem E4_checks : FCn.checkTm .nil LS_d.translate list_T.translate = true := by decide +kernel
/-- E5, `typecheck`. -/
theorem E5_checks : FCn.checkTm .nil SG_d.translate sngl_T.translate = true := by decide +kernel
/-- E6, gDOT's Fig. 2 in pDOT form, at `⊤`. -/
theorem E6_checks : FCn.checkTm .nil F2_d.translate Ty.top.translate = true := by decide +kernel
/-- E7, a module alias as a prefix. -/
theorem E7_checks : FCn.checkTm .nil E7_d.translate Ty.top.translate = true := by decide +kernel
/-- E8, replacement at an abstract member in both directions. -/
theorem E8_checks : FCn.checkTm .nil E8_d.translate Ty.top.translate = true := by decide +kernel
/-- E9, `x.a.b : ⊤` through the singleton `x.a : x.type`. -/
theorem E9_checks : FCn.checkPath e9_G.translate E9_xab_S.translatePath Ty.top.translate = true := by
  decide +kernel
/-- E10, one replacement step at each operand. -/
theorem E10_checks :
    FCn.checkPath e10_G.translate E10_pq.translatePath (e10_ty e10_p e10_q).translate = true ∧
    FCn.checkPath e10_G.translate E10_qp.translatePath (e10_ty e10_q e10_p).translate = true := by
  decide +kernel
/-- E11, Fld-I, at `T = ⊤`. -/
theorem E11_checks :
    FCn.checkPath (e11_G .top).translate (E11_d .top).translatePath
      (Ty.rcd (.trm e11_a (Ty.top).weaken.weaken)).translate = true := by
  decide +kernel
/-- E13, the cyclic object. -/
theorem E13_checks : FCn.checkTm .nil E13_cyclic_d.translate (Ty.mu e13_T).translate = true := by
  decide +kernel

/-! ## E12: one lookup at three levels -/

/-- X3's typed FCn store of E12 erases to the erased source store `γ12`. -/
theorem E12_store_erase : FCn.C0Ex.E12.σ.erase = γ12.erase := by decide +kernel

/-- `x.a.c` reaches `λ(z : ⊤) z` in the source store, on its erasure, and on the erasure of X3's
typed FCn store. -/
theorem E12_three :
    Lookups γ12 (.defp ((x12.sel e12_a).sel e12_c)) (.defv lam12) ∧
    PDot.Runtime.Lookups γ12.erase (.defp ((x12.sel e12_a).sel e12_c)) (.defv lam12.erase) ∧
    PDot.Runtime.Lookups FCn.C0Ex.E12.σ.erase (.defp ((x12.sel e12_a).sel e12_c)) (.defv lam12.erase) :=
  ⟨E12_lookup, E12_runtime, E12_store_erase ▸ E12_runtime⟩

/-! ## N1 to N5 at both levels -/

/-- N1's annotation `{a : {C : ∀(y : ⊤) ⊤ .. {c : ⊤}}} ∧ {b : {c : ⊤}}`, under its self. -/
abbrev n1_T : Ty ([],x) :=
  .and (.rcd (.trm n1_a (.rcd (.typ n1_C (.all .top .top) (.rcd (.trm n1_c .top))))))
       (.rcd (.trm n1_b (.rcd (.trm n1_c .top))))
/-- N2's annotation `{a : {A : ⊤..⊥}}`, under its self. -/
abbrev n2_T : Ty ([],x) := .rcd (.trm n2_a (.rcd (.typ n2_A .top .bot)))

/-- N1 in FCn: a literal at `tel` of N1's annotation whose field `b` holds a function has no type,
whatever the evidence of `a` and the function.  `DF-Fun` declares a function at a `Π`. -/
theorem N1_image_untyped (P : FCn.PathCo ([],x)) (v : FCn.Value ([],x)) (U : FCn.Ty []) :
    ¬ FCn.Value.HasType .nil (.obj n1_T.tel (.fld (.fld .nil n1_a (.path P)) n1_b (.fn v))) U := by
  intro h
  obtain ⟨_, hd⟩ := h.obj_inv
  obtain ⟨Tel, S, T, e, _, _, _⟩ := hd.fn_inv
  simp [Ty.tel, Ty.telAt, Dec.telAt, Dec.telP, Ty.translate, FCn.Telescope.append_cons, FCn.Telescope.append_nil,
    FCn.Telescope.rename, FCn.Pr.rename, FCn.Ty.rename] at e

/-- N1's candidate image erases to N1's literal when its evidence is at `x.a` and its function
erases to `λ(y) y`. -/
theorem N1_image_erase (P : FCn.PathCo ([],x)) (v : FCn.Value ([],x)) (hP : P.path = .sel (.var .here) n1_a)
    (hv : v.erase = .lam (.path (.var .here))) :
    (FCn.Value.obj n1_T.tel (.fld (.fld .nil n1_a (.path P)) n1_b (.fn v))).erase = badBoundsLit.erase := by
  show PDot.Runtime.Val.new (.cons (.cons .nil n1_a (.defp P.path)) n1_b (.defv v.erase)) = _
  rw [hP, hv]
  decide +kernel

/-- N1 at both levels. -/
theorem N1_both :
    (∀ U, ¬ Nonempty (HasTy .nil (.val badBoundsLit) U)) ∧
    ∀ P v U, ¬ FCn.Value.HasType .nil (.obj n1_T.tel (.fld (.fld .nil n1_a (.path P)) n1_b (.fn v))) U :=
  ⟨N1_bad_bounds, N1_image_untyped⟩

/-- N2 in FCn: a literal at `tel` of N2's annotation whose field holds a path has no type.
`DF-Path` declares a path at its singleton. -/
theorem N2_image_untyped (P : FCn.PathCo ([],x)) (U : FCn.Ty []) :
    ¬ FCn.Value.HasType .nil (.obj n2_T.tel (.fld .nil n2_a (.path P))) U := by
  intro h
  obtain ⟨_, hd⟩ := h.obj_inv
  obtain ⟨Tel, q, T, e, _, _, _⟩ := hd.path_inv
  simp [Ty.tel, Ty.telAt, Dec.telAt, Dec.telP, Ty.translate, FCn.Telescope.rename, FCn.Pr.rename,
    FCn.Ty.rename, FCn.Ty.sngl] at e

/-- N2's candidate image erases to N2's literal when its evidence is at `x.a`. -/
theorem N2_image_erase (P : FCn.PathCo ([],x)) (hP : P.path = .sel (.var .here) n2_a) :
    (FCn.Value.obj n2_T.tel (.fld .nil n2_a (.path P))).erase = fact2Lit.erase := by
  show PDot.Runtime.Val.new (.cons .nil n2_a (.defp P.path)) = _
  rw [hP]
  decide +kernel

/-- N2 at both levels. -/
theorem N2_both :
    (∀ U, ¬ Nonempty (HasTy .nil (.val fact2Lit) U)) ∧
    ∀ P U, ¬ FCn.Value.HasType .nil (.obj n2_T.tel (.fld .nil n2_a (.path P))) U :=
  ⟨N2_fact2, N2_image_untyped⟩

/-- The lookup of `x.zz` in the runtime store that holds N3's literal is stuck. -/
theorem n3_stuck (q : Path ([],x)) (hq : q = n3_xzz) :
    ∀ k, ¬ PDot.Runtime.LStep (PDot.Runtime.Store.nil.cons (.new (.cons .nil n3_h (.defp q)))) (.defp q) k := by
  subst hq
  intro k h
  generalize hp : (PDot.Runtime.Rhs.defp n3_xzz : PDot.Runtime.Rhs ([],x)) = k₀ at h
  cases h with
  | var => cases hp
  | selP h' =>
      cases hp
      cases PDot.Runtime.LStep.det h' .var
  | selV h' hg =>
      cases hp
      have e := PDot.Runtime.LStep.det h' .var
      cases e
      cases hg
  | selN h' _ =>
      cases hp
      cases PDot.Runtime.LStep.det h' .var

/-- N3 in FCn: a literal at `tel` of N3's annotation whose field holds a path has no type.  Its store
would be typed (`ST-Obj`), so the field's path `x.zz` would have a safe lookup (`path_safe`), and
that lookup is stuck (`n3_stuck`). -/
theorem N3_image_untyped (P : FCn.PathCo ([],x)) (U : FCn.Ty []) :
    ¬ FCn.Value.HasType .nil (.obj n3_T.tel (.fld .nil n3_h (.path P))) U := by
  intro h
  have h' := h
  obtain ⟨e, hd⟩ := h.obj_inv
  subst e
  have hσ := FCn.Store.Typed.obj FCn.Store.Typed.nil h'
  obtain ⟨Tel, q, T, e, hq, _, hP⟩ := hd.path_inv
  have e' : (FCn.Telescope.cons .nil (.fld n3_h (FCn.Ty.sngl ((Path.var .here).sel n3_zz))) :
      FCn.Telescope (([],x),x)) = Tel.cons (.fld n3_h (FCn.Ty.sngl q)) := e
  have e₁ := (FCn.Pr.fld.inj (FCn.Telescope.cons.inj e').2).2
  have e₂ := FCn.Pr.alias.inj (FCn.Telescope.cons.inj (FCn.Ty.mu.inj e₁)).2
  have e₃ : ((Path.var .here).sel n3_zz : Path (([],x),x)) = q := by
    have := congrArg (fun r => Path.substPath r (.var .here)) e₂
    simpa only [Paths.FCdot.Path.weaken_substPath] using this
  subst e₃
  have hq' : P.path = n3_xzz := hq
  have hs := FCn.path_safe hσ hP
  rcases hs _ .refl with ⟨v, hv⟩ | ⟨ds, hds⟩ | ⟨k, hk⟩
  · cases hv
  · cases hds
  · exact n3_stuck _ hq' k hk

/-- N3's candidate image erases to N3's literal when its evidence is at `x.zz`. -/
theorem N3_image_erase (P : FCn.PathCo ([],x)) (hP : P.path = n3_xzz) :
    (FCn.Value.obj n3_T.tel (.fld .nil n3_h (.path P))).erase = danglingLit.erase := by
  show PDot.Runtime.Val.new (.cons .nil n3_h (.defp P.path)) = _
  rw [hP]
  decide +kernel

/-- N3 at both levels. -/
theorem N3_both :
    (∀ U, ¬ Nonempty (HasTy .nil (.val danglingLit) U)) ∧
    ∀ P U, ¬ FCn.Value.HasType .nil (.obj n3_T.tel (.fld .nil n3_h (.path P))) U :=
  ⟨N3_dangling, N3_image_untyped⟩

/-- The type member of N4's context. -/
abbrev n4_A : Label := .typ 0

/-- N4 in FCn: `x : x.type` in `[x : ⟦{A : ⊤..⊤}⟧]`, by `PA-Sngl` over `PE-Refl`. -/
theorem N4_target_refl :
    FCn.checkPath (Ctx.nil.cons (.rcd (.typ n4_A .top .top))).translate
      (.sngl (.var .here) (.var .here) (.refl (.var .here))) (Ty.sngl (.var .here)).translate = true := by
  decide +kernel

/-- N4 at both levels: the source has no reflexive singleton, the target has one (decision 21). -/
theorem N4_both :
    ¬ Nonempty (HasTy (Ctx.nil.cons (.rcd (.typ n4_A .top .top))) (.path (.var .here)) (.sngl (.var .here))) ∧
    FCn.PathCo.HasType (Ctx.nil.cons (.rcd (.typ n4_A .top .top))).translate
      (.sngl (.var .here) (.var .here) (.refl (.var .here))) (Ty.sngl (.var .here)).translate :=
  ⟨N4_no_refl_sngl, FCn.checkPath_iff.1 N4_target_refl⟩

/-- N5 at both levels: `ty_def_new`'s third premise holds where `tight_bounds` fails, and the image
of those definitions is typed against the opened annotation only. -/
theorem N5_both :
    (∃ (T : Ty (([],x),x)) (ds : Defs (([],x),x)) (r : Path ([],x)),
      (Ty.mu T).tight = false ∧ Nonempty (DefsTy (Ctx.nil.cons .top) r (ds.substPath r) (T.substPath r))) ∧
    (∀ Δ, ¬ FCn.Defs.HasType Δ tightEx_r N5_third_premise.translate tightEx_T.tel) ∧
    FCn.Defs.HasType (FCn.Ctx.nil.cons (.opaque Ty.top.translate)) tightEx_r N5_third_premise.translate
      (tightEx_T.substPath tightEx_r).weaken.tel :=
  ⟨N5_tight, N5_image_untyped, N5_image_typed_opened⟩

end Nominal.Source
