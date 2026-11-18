import Coercions.CoDot.Core

/-!
# Safety of coercion evaluation on views

Canonical forms of typed views, then preservation and progress of coercion
evaluation under the store-shape invariant `Ctx.WF`, and termination by a
size measure with no typing assumption.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-! ## Helpers: coercion typing -/

theorem CoTy.anySubject'_aux {Γ : Ctx s} {o : Option (BVar s .var)} {c : Co s} {S T : Ty s}
    (h : CoTy Γ o c S T) : o = none → ∀ o', CoTy Γ o' c S T := by
  induction h with
  | id => intros; exact .id
  | top => intros; exact .top
  | bot => intros; exact .bot
  | seq _ _ ih1 ih2 => intro e o'; exact .seq (ih1 e o') (ih2 e o')
  | unfold => intro e; cases e
  | fold => intro e; cases e
  | andL _ ih => intro e o'; exact .andL (ih e o')
  | andR _ ih => intro e o'; exact .andR (ih e o')
  | pair _ _ ih1 ih2 => intro e o'; exact .pair (ih1 e o') (ih2 e o')
  | fld h1 _ => intros; exact .fld h1
  | typ h1 h2 _ _ => intros; exact .typ h1 h2
  | all h1 h2 _ _ => intros; exact .all h1 h2
  | up hk _ => intros; exact .up hk
  | down hk _ => intros; exact .down hk

/-- A coercion typed for no subject is typed for every subject. -/
theorem CoTy.anySubject' {Γ : Ctx s} {c : Co s} {S T : Ty s} (h : CoTy Γ none c S T)
    (o : Option (BVar s .var)) : CoTy Γ o c S T :=
  CoTy.anySubject'_aux h rfl o

/-! ## Helpers: records, labels, members, components -/

theorem labels_rename : ∀ (T : Ty s1) (ρ : Rename s1 s2), labels (T.rename ρ) = labels T
  | .top, _ => rfl
  | .bot, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .sel _ _, _ => rfl
  | .mu _, _ => rfl
  | .all _ _, _ => rfl
  | .and S T, ρ => by simp only [Ty.rename, labels, labels_rename S ρ, labels_rename T ρ]

theorem member_rename : ∀ (T : Ty s1) (ρ : Rename s1 s2) (A : Label),
    member (T.rename ρ) A = (member T A).map (fun U => U.rename ρ)
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .typ B S U, ρ, A => by
      simp only [Ty.rename, member]
      split <;> rfl
  | .fld _ _, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .all _ _, _, _ => rfl
  | .and S T, ρ, A => by
      simp only [Ty.rename, member, member_rename S ρ A, member_rename T ρ A]
      cases member T A <;> cases member S A <;> rfl

theorem Record.rename {T : Ty s1} (h : Record T) (ρ : Rename s1 s2) : Record (T.rename ρ) := by
  induction h with
  | typ => exact .typ
  | fld => exact .fld
  | and _ _ hd ih1 ih2 =>
      exact .and ih1 ih2 (by simpa only [labels_rename] using hd)

theorem member_labels : ∀ {T : Ty s} {A : Label} {U : Ty s}, member T A = some U → A ∈ labels T
  | .typ B _ _, A, U, h => by
      simp only [member] at h
      split at h
      · subst_vars; simp [labels]
      · cases h
  | .and S T, A, U, h => by
      simp only [member] at h
      simp only [labels, List.mem_append]
      cases h1 : member T A with
      | some V => exact .inr (member_labels h1)
      | none => rw [h1] at h; exact .inl (member_labels h)
  | .top, _, _, h => by simp [member] at h
  | .bot, _, _, h => by simp [member] at h
  | .fld _ _, _, _, h => by simp [member] at h
  | .sel _ _, _, _, h => by simp [member] at h
  | .mu _, _, _, h => by simp [member] at h
  | .all _ _, _, _, h => by simp [member] at h

theorem member_none {T : Ty s} {A : Label} (h : A ∉ labels T) : member T A = none := by
  cases h1 : member T A with
  | none => rfl
  | some U => exact absurd (member_labels h1) h

theorem Comp.trans {A B C : Ty s} (h1 : Comp A B) (h2 : Comp B C) : Comp A C := by
  induction h1 with
  | refl => exact h2
  | left _ ih => exact .left (ih h2)
  | right _ ih => exact .right (ih h2)

theorem Comp.labels_sub {R C : Ty s} (h : Comp R C) : ∀ ℓ, ℓ ∈ labels C → ℓ ∈ labels R := by
  induction h with
  | refl => exact fun _ h => h
  | left _ ih => intro ℓ h; simp only [labels, List.mem_append]; exact .inl (ih ℓ h)
  | right _ ih => intro ℓ h; simp only [labels, List.mem_append]; exact .inr (ih ℓ h)

theorem Comp.record {R C : Ty s} (h : Comp R C) (hr : Record R) : Record C := by
  induction h with
  | refl => exact hr
  | left _ ih => cases hr with | and h1 _ _ => exact ih h1
  | right _ ih => cases hr with | and _ h2 _ => exact ih h2

theorem Comp.member {R C : Ty s} (h : Comp R C) (hr : Record R) {A : Label} {U : Ty s}
    (hm : member C A = some U) : CoDot.member R A = some U := by
  induction h with
  | refl => exact hm
  | left hc ih =>
      cases hr with
      | and h1 _ hd =>
          have hT := member_none (hd A (hc.labels_sub A (member_labels hm)))
          simp only [CoDot.member]
          rw [hT, ih h1 hm]
          rfl
  | right _ ih =>
      cases hr with
      | and _ h2 _ =>
          simp only [CoDot.member, ih h2 hm]
          rfl

theorem Ctx.WF.lookup_cases {Γ : Ctx s} (wf : Γ.WF) {y : BVar s .var} {T : Ty s}
    (h : Γ.lookup y = T) : (∃ T0, T = .mu T0 ∧ Record T0) ∨ (∃ S U, T = .all S U) := by
  subst h
  rcases wf y with ⟨T0, hl, hr⟩ | ⟨S, U, hl⟩
  · exact .inl ⟨T0, hl, hr⟩
  · exact .inr ⟨S, U, hl⟩

theorem comp_record {Γ : Ctx s} (wf : Γ.WF) {x : BVar s .var} {T0 : Ty (s,x)}
    (hl : Γ.lookup x = .mu T0) : Record (T0.substVar x) := by
  rcases wf.lookup_cases hl with ⟨T0', h, hr⟩ | ⟨_, _, h⟩
  · cases h; exact hr.rename _
  · cases h

/-! ## Helpers: resolution -/

theorem Record.no_res {Γ : Ctx s} {x : BVar s .var} {C : Ty s} (h : Record C) :
    ∀ M, ¬ Res Γ x C M := by
  intro M r; cases h <;> cases r

theorem WrapTy.no_res {Γ : Ctx s} {x x' : BVar s .var} {k : Wrap s} {S N : Ty s}
    (h : WrapTy Γ x k S N) : ∀ M, ¬ Res Γ x' N M := by
  intro M r; cases h <;> cases r

theorem Res.det {Γ : Ctx s} {x : BVar s .var} {S M1 M2 : Ty s}
    (r1 : Res Γ x S M1) (r2 : Res Γ x S M2) : M1 = M2 := by
  cases r1 with
  | mu => cases r2; rfl
  | sel h1 m1 =>
      cases r2 with
      | sel h2 m2 =>
          rw [h1] at h2; cases h2
          rw [m1] at m2; cases m2; rfl

theorem ResStar.inv {Γ : Ctx s} {x : BVar s .var} {S C M : Ty s}
    (h : ResStar Γ x S C) (r : Res Γ x S M) : S = C ∨ ResStar Γ x M C := by
  cases h with
  | refl => exact .inl rfl
  | head r' h' => exact .inr (by rw [Res.det r r']; exact h')

theorem ResStar.normal {Γ : Ctx s} {x : BVar s .var} {S C : Ty s}
    (h : ResStar Γ x S C) (hn : ∀ M, ¬ Res Γ x S M) : S = C := by
  cases h with
  | refl => rfl
  | head r _ => exact absurd r (hn _)

/-! ## Helpers: views -/

/-- Views are closed under backward resolution. -/
theorem VTy.back {Γ : Ctx s} {w : View s} {S T : Ty s} (h : VTy Γ w T)
    (r : Res Γ w.loc S T) : VTy Γ w S := by
  cases h with
  | self h => exact .self (.head r h)
  | comp hl hc h => exact .comp hl hc (.head r h)
  | wrap hv hw h => exact .wrap hv hw (.head r h)
  | top h => exact .top (.head r h)

/-- Views are closed under forward resolution. -/
theorem VTy.fwd {Γ : Ctx s} (wf : Γ.WF) {w : View s} {S M : Ty s} (h : VTy Γ w S)
    (r : Res Γ w.loc S M) : VTy Γ w M := by
  cases h with
  | @self x _ h =>
      rcases ResStar.inv h r with rfl | h'
      · have r' : Res Γ x (Γ.lookup x) M := r
        rcases wf x with ⟨T0, hl, _⟩ | ⟨_, _, hl⟩
        · rw [hl] at r'; cases r'; exact .comp hl .refl .refl
        · rw [hl] at r'; cases r'
      · exact .self h'
  | comp hl hc h =>
      rcases ResStar.inv h r with rfl | h'
      · exact absurd r (Record.no_res (hc.record (comp_record wf hl)) _)
      · exact .comp hl hc h'
  | wrap hv hw h =>
      rcases ResStar.inv h r with rfl | h'
      · exact absurd r (hw.no_res _)
      · exact .wrap hv hw h'
  | top h =>
      rcases ResStar.inv h r with rfl | h'
      · cases r
      · exact .top h'

/-- Projections of a view at an intersection that is not a pair view. -/
theorem VTy.proj {Γ : Ctx s} (wf : Γ.WF) {w : View s} {S U : Ty s} (h : VTy Γ w (.and S U))
    (hw : ∀ c1 c2 ws', w.ws ≠ .pair c1 c2 :: ws') : VTy Γ w S ∧ VTy Γ w U := by
  cases h with
  | self h =>
      have := ResStar.normal h (fun M r => by cases r)
      rcases wf.lookup_cases this.symm with ⟨_, h, _⟩ | ⟨_, _, h⟩ <;> cases h
  | comp hl hc h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      exact ⟨.comp hl (hc.trans (.left .refl)) .refl, .comp hl (hc.trans (.right .refl)) .refl⟩
  | wrap hv hwt h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hwt with
      | pair => exact (hw _ _ _ rfl).elim
  | top h =>
      have := ResStar.normal h (fun M r => by cases r); cases this

/-! ## Canonical forms -/

/-- No view has type `⊥`. -/
theorem VTy.no_bot {Γ : Ctx s} (wf : Γ.WF) {w : View s} : ¬ VTy Γ w .bot := by
  intro h
  cases h with
  | self h =>
      have := ResStar.normal h (fun M r => by cases r)
      rcases wf.lookup_cases this.symm with ⟨_, h, _⟩ | ⟨_, _, h⟩ <;> cases h
  | comp hl hc h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hc.record (comp_record wf hl)
  | wrap hv hw h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hw
  | top h =>
      have := ResStar.normal h (fun M r => by cases r); cases this

/-- Canonical forms at a field type: a bare object whose record type has the
field as a component, or a `fld` wrapper over a view at a field type. -/
theorem VTy.canon_fld {Γ : Ctx s} (wf : Γ.WF) {x : BVar s .var} {ws : List (Wrap s)}
    {a : Label} {T : Ty s} (h : VTy Γ ⟨x, ws⟩ (.fld a T)) :
    (ws = [] ∧ ∃ T0, Γ.lookup x = .mu T0 ∧ Comp (T0.substVar x) (.fld a T)) ∨
    (∃ c ws' T1, ws = .fld a c :: ws' ∧ VTy Γ ⟨x, ws'⟩ (.fld a T1) ∧ CoTy Γ none c T1 T) := by
  cases h with
  | self h =>
      have := ResStar.normal h (fun M r => by cases r)
      rcases wf.lookup_cases this.symm with ⟨_, h, _⟩ | ⟨_, _, h⟩ <;> cases h
  | comp hl hc h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      exact .inl ⟨rfl, _, hl, hc⟩
  | wrap hv hw h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hw with
      | fld hc => exact .inr ⟨_, _, _, rfl, hv, hc⟩
  | top h =>
      have := ResStar.normal h (fun M r => by cases r); cases this

/-- Canonical forms at a function type: a bare function at exactly this type,
or an `all` wrapper over a view at a function type. -/
theorem VTy.canon_all {Γ : Ctx s} (wf : Γ.WF) {x : BVar s .var} {ws : List (Wrap s)}
    {S : Ty s} {T : Ty (s,x)} (h : VTy Γ ⟨x, ws⟩ (.all S T)) :
    (ws = [] ∧ Γ.lookup x = .all S T) ∨
    (∃ c d ws' S1 T1, ws = .all c d :: ws' ∧ VTy Γ ⟨x, ws'⟩ (.all S1 T1) ∧
      CoTy Γ none c S S1 ∧ CoTy (Γ.cons S) none d T1 T) := by
  cases h with
  | self h =>
      have := ResStar.normal h (fun M r => by cases r)
      exact .inl ⟨rfl, this.symm⟩
  | comp hl hc h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hc.record (comp_record wf hl)
  | wrap hv hw h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hw with
      | all hc hd => exact .inr ⟨_, _, _, _, _, rfl, hv, hc, hd⟩
  | top h =>
      have := ResStar.normal h (fun M r => by cases r); cases this

/-- Canonical forms at a type-member type: a bare object that defines `A`
precisely at both bounds, or a `typ` wrapper over a view at a type-member type. -/
theorem VTy.canon_typ {Γ : Ctx s} (wf : Γ.WF) {x : BVar s .var} {ws : List (Wrap s)}
    {A : Label} {S T : Ty s} (h : VTy Γ ⟨x, ws⟩ (.typ A S T)) :
    (ws = [] ∧ ∃ T0 U, Γ.lookup x = .mu T0 ∧ member T0 A = some U ∧
      S = U.substVar x ∧ T = U.substVar x) ∨
    (∃ c d ws' S1 T1, ws = .typ A c d :: ws' ∧ VTy Γ ⟨x, ws'⟩ (.typ A S1 T1) ∧
      CoTy Γ none c S S1 ∧ CoTy Γ none d T1 T) := by
  cases h with
  | self h =>
      have := ResStar.normal h (fun M r => by cases r)
      rcases wf.lookup_cases this.symm with ⟨_, h, _⟩ | ⟨_, _, h⟩ <;> cases h
  | @comp x T0 C _ hl hc h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      have hR := comp_record wf hl
      have hC := hc.record hR
      cases hC
      have hm := hc.member hR (A := A) (U := S) (by simp [member])
      rw [Ty.substVar, member_rename] at hm
      cases hm0 : member T0 A with
      | none => rw [hm0] at hm; cases hm
      | some U =>
          rw [hm0] at hm
          cases hm
          exact .inl ⟨rfl, T0, U, hl, hm0, rfl, rfl⟩
  | wrap hv hw h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hw with
      | typ hc hd => exact .inr ⟨_, _, _, _, _, rfl, hv, hc, hd⟩
  | top h =>
      have := ResStar.normal h (fun M r => by cases r); cases this

/-- Projection of a pair view: the view is typed at exactly the wrapper's
target, so each projection meets the coercion of its own component. -/
theorem VTy.canon_pair {Γ : Ctx s} (_wf : Γ.WF) {x : BVar s .var} {ws : List (Wrap s)}
    {c1 c2 : Co s} {T U : Ty s} (h : VTy Γ ⟨x, .pair c1 c2 :: ws⟩ (.and T U)) :
    ∃ S, VTy Γ ⟨x, ws⟩ S ∧ CoTy Γ (some x) c1 S T ∧ CoTy Γ (some x) c2 S U := by
  cases h with
  | wrap hv hw h =>
      have := ResStar.normal h (fun M r => by cases r); subst this
      cases hw with
      | pair hc hd => exact ⟨_, hv, hc, hd⟩
  | top h =>
      have := ResStar.normal h (fun M r => by cases r); cases this

/-! ## Preservation and progress -/

/-- Preservation for coercion evaluation. It holds for every store predicate
`D`: the store premises of the two `obj` rules are not used. -/
theorem Step.preservation {Γ : Ctx s} (wf : Γ.WF) {D : BVar s .var → Label → Prop}
    {e e' : Ev s} {T : Ty s}
    (h : EvTy Γ e T) (st : Step D e e') : EvTy Γ e' T ∧ e'.loc = e.loc := by
  induction st generalizing T with
  | appCtx _ ih =>
      cases h with
      | app he hc =>
          obtain ⟨he', hl⟩ := ih he
          exact ⟨.app he' (by rw [hl]; exact hc), hl⟩
  | upSubj _ ih =>
      cases h with
      | up he hev hl =>
          obtain ⟨he', hl'⟩ := ih he
          exact ⟨.up he' hev hl, hl'⟩
  | upEv _ ih =>
      cases h with
      | up he hev hl =>
          obtain ⟨hev', hl'⟩ := ih hev
          exact ⟨.up he hev' (hl'.trans hl), rfl⟩
  | downSubj _ ih =>
      cases h with
      | down he hev hl =>
          obtain ⟨he', hl'⟩ := ih he
          exact ⟨.down he' hev hl, hl'⟩
  | downEv _ ih =>
      cases h with
      | down he hev hl =>
          obtain ⟨hev', hl'⟩ := ih hev
          exact ⟨.down he hev' (hl'.trans hl), rfl⟩
  | id =>
      cases h with
      | app he hc => cases hc; exact ⟨he, rfl⟩
  | top =>
      cases h with
      | app he hc => cases hc; exact ⟨.ret (.top .refl), rfl⟩
  | unfold =>
      cases h with
      | app he hc =>
          cases hc
          cases he with
          | ret hv => exact ⟨.ret (hv.fwd wf .mu), rfl⟩
  | fold =>
      cases h with
      | app he hc =>
          cases hc
          cases he with
          | ret hv => exact ⟨.ret (hv.back .mu), rfl⟩
  | seq =>
      cases h with
      | app he hc =>
          cases hc with
          | seq h1 h2 => exact ⟨.app (.app he h1) h2, rfl⟩
  | andLPair =>
      cases h with
      | app he hc =>
          cases hc with
          | andL hc =>
              cases he with
              | ret hv =>
                  obtain ⟨_, hv', h1, _⟩ := VTy.canon_pair wf hv
                  exact ⟨.app (.app (.ret hv') h1) hc, rfl⟩
  | andLOther hne =>
      cases h with
      | app he hc =>
          cases hc with
          | andL hc =>
              cases he with
              | ret hv => exact ⟨.app (.ret (VTy.proj wf hv hne).1) hc, rfl⟩
  | andRPair =>
      cases h with
      | app he hc =>
          cases hc with
          | andR hc =>
              cases he with
              | ret hv =>
                  obtain ⟨_, hv', _, h2⟩ := VTy.canon_pair wf hv
                  exact ⟨.app (.app (.ret hv') h2) hc, rfl⟩
  | andROther hne =>
      cases h with
      | app he hc =>
          cases hc with
          | andR hc =>
              cases he with
              | ret hv => exact ⟨.app (.ret (VTy.proj wf hv hne).2) hc, rfl⟩
  | pair =>
      cases h with
      | app he hc =>
          cases hc with
          | pair h1 h2 =>
              cases he with
              | ret hv => exact ⟨.ret (.wrap hv (.pair h1 h2) .refl), rfl⟩
  | fld =>
      cases h with
      | app he hc =>
          cases hc with
          | fld h1 =>
              cases he with
              | ret hv => exact ⟨.ret (.wrap hv (.fld h1) .refl), rfl⟩
  | typ =>
      cases h with
      | app he hc =>
          cases hc with
          | typ h1 h2 =>
              cases he with
              | ret hv => exact ⟨.ret (.wrap hv (.typ h1 h2) .refl), rfl⟩
  | all =>
      cases h with
      | app he hc =>
          cases hc with
          | all h1 h2 =>
              cases he with
              | ret hv => exact ⟨.ret (.wrap hv (.all h1 h2) .refl), rfl⟩
  | upStart =>
      cases h with
      | app he hc =>
          cases hc with
          | up hk => exact ⟨.up he (.app (.ret (.self .refl)) hk) rfl, rfl⟩
  | downStart =>
      cases h with
      | app he hc =>
          cases hc with
          | down hk => exact ⟨.down he (.app (.ret (.self .refl)) hk) rfl, rfl⟩
  | upObj =>
      cases h with
      | up he hev hloc =>
          cases he with
          | ret hv =>
              cases hev with
              | ret hv' =>
                  simp only [Ev.loc] at hloc; subst hloc
                  rcases VTy.canon_typ wf hv' with ⟨_, _, _, hl', hm', -, rfl⟩ | ⟨_, _, _, _, _, h, -⟩
                  · exact ⟨.ret (hv.fwd wf (.sel hl' hm')), rfl⟩
                  · cases h
  | upTyp =>
      cases h with
      | up he hev hloc =>
          cases he with
          | ret hv =>
              cases hev with
              | ret hv' =>
                  simp only [Ev.loc] at hloc; subst hloc
                  rcases VTy.canon_typ wf hv' with ⟨h, -⟩ | ⟨_, _, _, _, _, h, hv'', _, hd⟩
                  · cases h
                  · cases h
                    exact ⟨.app (.up (.ret hv) (.ret hv'') rfl) (hd.anySubject' _), rfl⟩
  | downObj =>
      cases h with
      | down he hev hloc =>
          cases he with
          | ret hv =>
              cases hev with
              | ret hv' =>
                  simp only [Ev.loc] at hloc; subst hloc
                  rcases VTy.canon_typ wf hv' with ⟨_, _, _, hl', hm', rfl, -⟩ | ⟨_, _, _, _, _, h, -⟩
                  · exact ⟨.ret (hv.back (.sel hl' hm')), rfl⟩
                  · cases h
  | downTyp =>
      cases h with
      | down he hev hloc =>
          cases he with
          | ret hv =>
              cases hev with
              | ret hv' =>
                  simp only [Ev.loc] at hloc; subst hloc
                  rcases VTy.canon_typ wf hv' with ⟨h, -⟩ | ⟨_, _, _, _, _, h, hv'', hc, _⟩
                  · cases h
                  · cases h
                    exact ⟨.down (.app (.ret hv) (hc.anySubject' _)) (.ret hv'') rfl, rfl⟩

/-- Progress for coercion evaluation, when the store defines at least the
type members that the context's object types declare. -/
theorem EvTy.progress {Γ : Ctx s} (wf : Γ.WF) {D : BVar s .var → Label → Prop}
    (hD : ∀ y A, Γ.Defines y A → D y A) {e : Ev s} {T : Ty s} (h : EvTy Γ e T) :
    (∃ w, e = .ret w) ∨ ∃ e', Step D e e' := by
  induction h with
  | ret => exact .inl ⟨_, rfl⟩
  | app he hc ih =>
      right
      rcases ih with ⟨⟨x, ws⟩, rfl⟩ | ⟨e', st⟩
      · cases hc with
        | id => exact ⟨_, .id⟩
        | top => exact ⟨_, .top⟩
        | bot =>
            cases he with
            | ret hv => exact absurd hv (VTy.no_bot wf)
        | seq => exact ⟨_, .seq⟩
        | unfold => exact ⟨_, .unfold⟩
        | fold => exact ⟨_, .fold⟩
        | andL =>
            by_cases hp : ∃ c1 c2 ws', ws = .pair c1 c2 :: ws'
            · obtain ⟨_, _, _, rfl⟩ := hp
              exact ⟨_, .andLPair⟩
            · exact ⟨_, .andLOther (fun c1 c2 ws' h => hp ⟨c1, c2, ws', h⟩)⟩
        | andR =>
            by_cases hp : ∃ c1 c2 ws', ws = .pair c1 c2 :: ws'
            · obtain ⟨_, _, _, rfl⟩ := hp
              exact ⟨_, .andRPair⟩
            · exact ⟨_, .andROther (fun c1 c2 ws' h => hp ⟨c1, c2, ws', h⟩)⟩
        | pair => exact ⟨_, .pair⟩
        | fld => exact ⟨_, .fld⟩
        | typ => exact ⟨_, .typ⟩
        | all => exact ⟨_, .all⟩
        | up => exact ⟨_, .upStart⟩
        | down => exact ⟨_, .downStart⟩
      · exact ⟨_, .appCtx st⟩
  | up _ hev _ ih1 ih2 =>
      right
      rcases ih1 with ⟨w, rfl⟩ | ⟨e', st⟩
      · rcases ih2 with ⟨⟨y, ws⟩, rfl⟩ | ⟨ev', st⟩
        · cases hev with
          | ret hv =>
              rcases VTy.canon_typ wf hv with ⟨rfl, _, _, hl, hm, -, -⟩ | ⟨_, _, _, _, _, rfl, -⟩
              · exact ⟨_, .upObj (hD _ _ ⟨_, _, hl, hm⟩)⟩
              · exact ⟨_, .upTyp⟩
        · exact ⟨_, .upEv st⟩
      · exact ⟨_, .upSubj st⟩
  | down _ hev _ ih1 ih2 =>
      right
      rcases ih1 with ⟨w, rfl⟩ | ⟨e', st⟩
      · rcases ih2 with ⟨⟨y, ws⟩, rfl⟩ | ⟨ev', st⟩
        · cases hev with
          | ret hv =>
              rcases VTy.canon_typ wf hv with ⟨rfl, _, _, hl, hm, -, -⟩ | ⟨_, _, _, _, _, rfl, -⟩
              · exact ⟨_, .downObj (hD _ _ ⟨_, _, hl, hm⟩)⟩
              · exact ⟨_, .downTyp⟩
        · exact ⟨_, .downEv st⟩
      · exact ⟨_, .downSubj st⟩

/-! ## Termination, with no typing assumption

A pending coercion weighs more than the same coercion stored in a wrapper,
and a wrapper weighs more than its parts. Every step lowers the measure. -/

/-- The weight of a pending coercion. -/
def Co.pend : Co s → Nat
  | .id => 1
  | .top => 1
  | .bot => 1
  | .unfold => 1
  | .fold => 1
  | .seq c d => c.pend + d.pend + 1
  | .andL c => c.pend + 1
  | .andR c => c.pend + 1
  | .pair c d => c.pend + d.pend + 2
  | .fld _ c => c.pend + 2
  | .typ _ c d => c.pend + d.pend + 2
  | .all c d => c.pend + d.pend + 2
  | .up _ _ k => k.pend + 2
  | .down _ _ k => k.pend + 2

/-- The weight of a stored wrapper: the pending weight of its coercion minus one. -/
def Wrap.stored : Wrap s → Nat
  | .fld _ c => c.pend + 1
  | .typ _ c d => c.pend + d.pend + 1
  | .all c d => c.pend + d.pend + 1
  | .pair c d => c.pend + d.pend + 1

def Wrap.listWeight : List (Wrap s) → Nat
  | [] => 0
  | k :: ws => k.stored + Wrap.listWeight ws

def Ev.measure : Ev s → Nat
  | .ret w => Wrap.listWeight w.ws
  | .app e c => e.measure + c.pend
  | .up e _ ev => e.measure + ev.measure + 1
  | .down e _ ev => e.measure + ev.measure + 1

theorem Step.measure_lt {D : BVar s .var → Label → Prop} {e e' : Ev s} (st : Step D e e') :
    e'.measure < e.measure := by
  induction st <;>
    simp only [Ev.measure, Co.pend, Wrap.stored, Wrap.listWeight] at * <;> omega

end CoDot
