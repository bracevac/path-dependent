import Coercions.CoDot.Core

/-!
# Coerced substitution for coercion typing

A coerced renaming sends each variable to a variable under a coercion.
Coercion typing is preserved by renamings and by typed coerced renamings;
narrowing and substitution of a variable are both instances.
`app_all_wrapper` is the instance used by application through an `all`
wrapper with a coerced argument.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

theorem CoTy.anySubject_aux {Γ : Ctx s} {o : Option (BVar s .var)} {c : Co s} {S T : Ty s}
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

/-- A coercion typed for any subject is typed for each subject. -/
theorem CoTy.anySubject {Γ : Ctx s} {c : Co s} {S T : Ty s} (h : CoTy Γ none c S T)
    (o : Option (BVar s .var)) : CoTy Γ o c S T :=
  CoTy.anySubject_aux h rfl o

/-- Renaming under lookup preservation. -/
theorem CoTy.rename {Γ1 : Ctx s1} {Γ2 : Ctx s2} {ρ : Rename s1 s2}
    (hρ : ∀ x, Γ2.lookup (ρ.var x) = (Γ1.lookup x).rename ρ)
    {o : Option (BVar s1 .var)} {c : Co s1} {S T : Ty s1} (h : CoTy Γ1 o c S T) :
    CoTy Γ2 (o.map ρ.var) (c.rename ρ) (S.rename ρ) (T.rename ρ) := by
  induction h generalizing s2 Γ2 with
  | id => exact .id
  | top => exact .top
  | bot => exact .bot
  | seq _ _ ih1 ih2 => exact .seq (ih1 hρ) (ih2 hρ)
  | unfold => rw [Ty.substVar_rename]; exact .unfold
  | fold => rw [Ty.substVar_rename]; exact .fold
  | andL _ ih => exact .andL (ih hρ)
  | andR _ ih => exact .andR (ih hρ)
  | pair _ _ ih1 ih2 => exact .pair (ih1 hρ) (ih2 hρ)
  | fld _ ih => exact .fld (ih hρ)
  | typ _ _ ih1 ih2 => exact .typ (ih1 hρ) (ih2 hρ)
  | @all _ Γ1 c S2 S1 d T1 T2 _ _ _ ih1 ih2 =>
    have hl : ∀ x, (Γ2.cons (S2.rename ρ)).lookup (ρ.lift.var x)
        = ((Γ1.cons S2).lookup x).rename ρ.lift := by
      intro x
      cases x with
      | here => exact (Ty.weaken_rename S2 ρ).symm
      | there y =>
        show (Γ2.lookup (ρ.var y)).weaken = (Γ1.lookup y).weaken.rename ρ.lift
        rw [hρ y, Ty.weaken_rename]
    exact .all (ih1 hρ) (ih2 hl)
  | @up _ Γ1 x k A S T _ _ ih =>
    have h := ih hρ
    rw [← hρ x] at h
    exact .up h
  | @down _ Γ1 x k A S T _ _ ih =>
    have h := ih hρ
    rw [← hρ x] at h
    exact .down h

/-- Lifting a typed coerced renaming under a binder. -/
theorem CoSub.Ok.lift {Γ1 : Ctx s1} {Γ2 : Ctx s2} {σ : CoSub s1 s2} (hσ : CoSub.Ok Γ1 Γ2 σ)
    (S : Ty s1) : CoSub.Ok (Γ1.cons S) (Γ2.cons (S.rename σ.ρ)) σ.lift := by
  intro x
  cases x with
  | here =>
    show CoTy _ _ .id (S.rename σ.ρ).weaken (S.weaken.rename σ.ρ.lift)
    rw [Ty.weaken_rename]; exact .id
  | there y =>
    show CoTy _ _ ((σ.η y).rename Rename.succ) ((Γ2.lookup (σ.ρ.var y)).rename Rename.succ)
      ((Γ1.lookup y).weaken.rename σ.ρ.lift)
    rw [Ty.weaken_rename]
    exact CoTy.rename (Γ2 := Γ2.cons (S.rename σ.ρ)) (ρ := Rename.succ) (fun _ => rfl) (hσ y)

/-- Coerced substitution: typing of coercions is preserved by a typed coerced
renaming. Narrowing and substitution of a variable are both instances. -/
theorem CoTy.csubst {Γ1 : Ctx s1} {Γ2 : Ctx s2} {σ : CoSub s1 s2} (hσ : CoSub.Ok Γ1 Γ2 σ)
    {o : Option (BVar s1 .var)} {c : Co s1} {S T : Ty s1} (h : CoTy Γ1 o c S T) :
    CoTy Γ2 (o.map σ.ρ.var) (c.csubst σ) (S.rename σ.ρ) (T.rename σ.ρ) := by
  induction h generalizing s2 Γ2 with
  | id => exact .id
  | top => exact .top
  | bot => exact .bot
  | seq _ _ ih1 ih2 => exact .seq (ih1 hσ) (ih2 hσ)
  | unfold => rw [Ty.substVar_rename]; exact .unfold
  | fold => rw [Ty.substVar_rename]; exact .fold
  | andL _ ih => exact .andL (ih hσ)
  | andR _ ih => exact .andR (ih hσ)
  | pair _ _ ih1 ih2 => exact .pair (ih1 hσ) (ih2 hσ)
  | fld _ ih => exact .fld (ih hσ)
  | typ _ _ ih1 ih2 => exact .typ (ih1 hσ) (ih2 hσ)
  | all _ _ ih1 ih2 => exact .all (ih1 hσ) (ih2 (hσ.lift _))
  | @up _ Γ1 x k A S T _ _ ih => exact .up (.seq (hσ x) (ih hσ))
  | @down _ Γ1 x k A S T _ _ ih => exact .down (.seq (hσ x) (ih hσ))

/-- Instantiating a parameter of type `S` by a reference `z ▷ e` at `S`. -/
theorem CoSub.inst_ok {Γ : Ctx s} {S : Ty s} {z : BVar s .var} {e : Co s}
    (he : CoTy Γ (some z) e (Γ.lookup z) S) : CoSub.Ok (Γ.cons S) Γ (CoSub.inst z e) := by
  intro x
  cases x with
  | here =>
    show CoTy Γ (some z) e (Γ.lookup z) (S.weaken.substVar z)
    rw [Ty.weaken_substVar]; exact he
  | there y =>
    show CoTy Γ (some y) .id (Γ.lookup y) ((Γ.lookup y).weaken.substVar z)
    rw [Ty.weaken_substVar]; exact .id

/-- Dependent application through an `all` wrapper with a coerced argument.
The function view `f ▷ (all c d :: ws)` is applied to the reference `z ▷ e`.
The inner view receives `z ▷ seq e c`; the result is coerced by `d` with its
parameter instantiated by `z ▷ e`. The result type is opened at the same
location `z` before and after the step. `h` is the conclusion of
`VTy.canon_all` in the wrapper case. -/
theorem app_all_wrapper {Γ : Ctx s} {S S1 : Ty s} {T T1 : Ty (s,x)} {c : Co s} {d : Co (s,x)}
    {z : BVar s .var} {e : Co s}
    (hc : CoTy Γ none c S S1) (hd : CoTy (Γ.cons S) none d T1 T)
    (he : CoTy Γ (some z) e (Γ.lookup z) S) :
    CoTy Γ (some z) (.seq e c) (Γ.lookup z) S1 ∧
    CoTy Γ none (d.csubst (CoSub.inst z e)) (T1.substVar z) (T.substVar z) :=
  ⟨.seq he (hc.anySubject _), CoTy.csubst (CoSub.inst_ok he) hd⟩

end CoDot
