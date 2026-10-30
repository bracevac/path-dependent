import Coercions.Nominal.Source.Binding

/-!
# Replacement and tight bounds

Replacement `p ↦ q ⊢ T ⇝ T'` is Coq's `repl_typ` and `repl_dec` (`Definitions.v:379-411`).  `T'` is
`T` with one occurrence of a path that starts with `p` rewritten to start with `q`.  There is one Lean
constructor per Coq constructor, in Coq's order.  Coq's paths are named, so its `rbnd` and `rall2`
keep `p` and `q` as they are.  A de Bruijn path that crosses a binder is weakened, so here the two
rules ask for `p↑ ↦ q↑` under the binder.

The hole of a replacement is a type with one new variable `h`, the innermost.  Opened at `p` it is
`T`.  Opened at `q` it is `T'` (`Repl.hole_spec`).  Three lemmas of `Replacement.v` follow:
`Repl.swap` (`repl_swap`), `repl_intro_sngl`, and `Repl.subst` (`repl_typ_subst`, here along any path
substitution).  `Ty.isRepl` decides the relation (`Ty.isRepl_iff`).  `repl_one_occurrence` shows
that the relation rewrites one occurrence and refuses two at once.

`tight_bounds` (`Definitions.v:564-575`) is the Boolean function `Ty.tight`.  Every path substitution
keeps it (`Ty.tight_subst`).  `tight_premise_independent` shows that it does not follow from the
opened annotation: an annotation that is not tight opens to a tight type.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Replacement (`Definitions.v:379-411`) -/

mutual
/-- `p ↦ q ⊢ T ⇝ T'`, Coq's `repl_typ p q T T'`. -/
inductive Repl : Path s → Path s → Ty s → Ty s → Type where
  | rrcd : ReplDec p q D₁ D₂ → Repl p q (.rcd D₁) (.rcd D₂)                 -- :380
  | rand1 : Repl p q T₁ T₂ → Repl p q (.and T₁ U) (.and T₂ U)                -- :383
  | rand2 : Repl p q T₁ T₂ → Repl p q (.and U T₁) (.and U T₂)                -- :386
  | rpath : Repl p q (.sel (p.nomExt bs) A) (.sel (q.nomExt bs) A)                 -- :389, (p.bs).A
  | rbnd : Repl p.weaken q.weaken T₁ T₂ → Repl p q (.mu T₁) (.mu T₂)         -- :391, under z of μ(z. _)
  | rall1 : Repl p q T₁ T₂ → Repl p q (.all T₁ U) (.all T₂ U)                -- :394, ∀(z : _) U
  | rall2 : Repl p.weaken q.weaken T₁ T₂ → Repl p q (.all U T₁) (.all U T₂)  -- :397, under z of ∀(z : U) _
  | rsngl : Repl p q (.sngl (p.nomExt bs)) (.sngl (q.nomExt bs))                   -- :400, (p.bs).type
/-- `p ↦ q ⊢ D ⇝ᵈ D'`, Coq's `repl_dec p q D D'`. -/
inductive ReplDec : Path s → Path s → Dec s → Dec s → Type where
  | rdtyp1 : Repl p q T₁ T₂ → ReplDec p q (.typ A T₁ U) (.typ A T₂ U)        -- :403, lower bound
  | rdtyp2 : Repl p q T₁ T₂ → ReplDec p q (.typ A U T₁) (.typ A U T₂)        -- :406, upper bound
  | rdtrm : Repl p q T₁ T₂ → ReplDec p q (.trm a T₁) (.trm a T₂)             -- :409
end

/-! ## Tight bounds (`Definitions.v:564-575`) -/

mutual
/-- `tight_bounds`: every type member reached through records, intersections, field types and `μ`
has equal bounds.  It does not look inside a `∀` or inside the bounds of a type member.  Coq's last
case `_ => True` is written out, one line per constructor. -/
def Ty.tight : Ty s → Bool
  | .top => true                                 -- ⊤.tight = true
  | .bot => true                                 -- ⊥.tight = true
  | .rcd D => D.tight                            -- {D}.tight = D.tight
  | .and T U => T.tight && U.tight               -- (T ∧ U).tight = T.tight && U.tight
  | .sel _ _ => true                             -- (p.A).tight = true
  | .mu T => T.tight                             -- (μ(z. T)).tight = T.tight
  | .all _ _ => true                             -- (∀(z : S) T).tight = true
  | .sngl _ => true                              -- (p.type).tight = true
/-- `tight_bounds_dec`. -/
def Dec.tight : Dec s → Bool
  | .typ _ T U => decide (T = U)                 -- {A : T..U}.tight = (T == U)
  | .trm _ T => T.tight                          -- {a : T}.tight = T.tight
end

/-! ## The hole of a replacement

`r.hole : Ty (s,h)` has the hole variable `h` as its innermost variable.  `rpath` and `rsngl` put `h`
in place of the prefix.  Every congruence rebuilds its former with the untouched part weakened past
`h`.  For `rall1` the untouched part is the codomain, which sits under the binder `z`, so it is
weakened under `z`.  Under `μ` and `∀` the hole variable is exchanged past the binder by
`Rename.swap`, which exchanges the two innermost variables. -/

mutual
def Repl.hole {p q : Path s} {T T' : Ty s} : Repl p q T T' → Ty (s,x)
  | .rrcd r => .rcd r.hole
  | .rand1 (U := U) r => .and r.hole U.weaken
  | .rand2 (U := U) r => .and U.weaken r.hole
  | .rpath (bs := bs) (A := A) => .sel ((Path.var .here).nomExt bs) A
  | .rbnd r => .mu (r.hole.rename Rename.swap)                       -- hole variable h moved past z of μ(z. _)
  | .rall1 (U := U) r => .all r.hole (U.rename Rename.succ.lift)     -- U weakened under z of ∀(z : _) U
  | .rall2 (U := U) r => .all U.weaken (r.hole.rename Rename.swap)   -- hole variable h moved past z of ∀(z : U) _
  | .rsngl (bs := bs) => .sngl ((Path.var .here).nomExt bs)
def ReplDec.hole {p q : Path s} {D D' : Dec s} : ReplDec p q D D' → Dec (s,x)
  | .rdtyp1 (A := A) (U := U) r => .typ A r.hole U.weaken
  | .rdtyp2 (A := A) (U := U) r => .typ A U.weaken r.hole
  | .rdtrm (a := a) r => .trm a r.hole
end

theorem Ty.rename_eq_subst (T : Ty s₁) (ρ : Rename s₁ s₂) :
    T.rename ρ = T.subst (PathSubst.ofRename ρ) :=
  (Ty.subst_ofRename T ρ).symm

theorem Ty.subst_ofRename_id (T : Ty s) : T.subst (PathSubst.ofRename Rename.id) = T := by
  rw [Ty.subst_ofRename, Ty.rename_id]

/-- Exchanging the hole variable past a binder, then opening it at `u` under the binder, is opening
at `u↑`. -/
theorem PathSubst.ofRename_swap_comp_one_lift (u : Path s) :
    (PathSubst.ofRename (Rename.swap (s := s) (k1 := .var) (k2 := .var))).comp (PathSubst.one u).lift
      = PathSubst.one (u.weaken (k := .var)) := by
  apply PathSubst.funext'
  intro y
  rcases y with _ | ⟨_ | y⟩ <;> rfl

/-- Weakening past the hole variable under a binder, then opening the hole under the binder, is the
identity. -/
theorem PathSubst.ofRename_succ_lift_comp_one_lift (u : Path s) :
    (PathSubst.ofRename ((Rename.succ (s := s) (k := .var)).lift (k := .var))).comp
        (PathSubst.one u).lift
      = PathSubst.ofRename Rename.id := by
  apply PathSubst.funext'
  intro y
  rcases y with _ | ⟨_ | y⟩ <;> rfl

theorem Path.here_ext_subst_one (u : Path s) (bs : List Label) :
    ((Path.var .here : Path (s,x)).nomExt bs).subst (PathSubst.one u) = u.nomExt bs := by
  rw [Path.ext_subst]
  rfl

mutual
/-- The hole opened at `u` is the left side when `u = p` and the right side when `u = q`. -/
theorem Repl.hole_open : ∀ {p q : Path s} {T T' : Ty s} (r : Repl p q T T') (u : Path s),
    (u = p → r.hole.substPath u = T) ∧ (u = q → r.hole.substPath u = T')
  | _, _, _, _, .rrcd r, u => by
      have ih := ReplDec.hole_open r u
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst] <;>
      rw [← Dec.substPath]
      · rw [ih.1 h]
      · rw [ih.2 h]
  | _, _, _, _, .rand1 (U := U) r, u => by
      have ih := Repl.hole_open r u
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst] <;>
      rw [← Ty.substPath, ← Ty.substPath, Ty.weaken_substPath]
      · rw [ih.1 h]
      · rw [ih.2 h]
  | _, _, _, _, .rand2 (U := U) r, u => by
      have ih := Repl.hole_open r u
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst] <;>
      rw [← Ty.substPath, ← Ty.substPath, Ty.weaken_substPath]
      · rw [ih.1 h]
      · rw [ih.2 h]
  | _, _, _, _, .rpath (bs := bs) (A := A), u => by
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst, Path.here_ext_subst_one]
  | _, _, _, _, .rbnd r, u => by
      have ih := Repl.hole_open r u.weaken
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst] <;>
      rw [Ty.rename_eq_subst, Ty.subst_subst, PathSubst.ofRename_swap_comp_one_lift, ← Ty.substPath]
      · rw [ih.1 (by rw [h])]
      · rw [ih.2 (by rw [h])]
  | _, _, _, _, .rall1 (U := U) r, u => by
      have ih := Repl.hole_open r u
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst] <;>
      rw [Ty.rename_eq_subst U, Ty.subst_subst, PathSubst.ofRename_succ_lift_comp_one_lift,
        Ty.subst_ofRename_id, ← Ty.substPath]
      · rw [ih.1 h]
      · rw [ih.2 h]
  | _, _, _, _, .rall2 (U := U) r, u => by
      have ih := Repl.hole_open r u.weaken
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst] <;>
      rw [Ty.rename_eq_subst _ Rename.swap, Ty.subst_subst, PathSubst.ofRename_swap_comp_one_lift,
        ← Ty.substPath, ← Ty.substPath, Ty.weaken_substPath]
      · rw [ih.1 (by rw [h])]
      · rw [ih.2 (by rw [h])]
  | _, _, _, _, .rsngl (bs := bs), u => by
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;>
      simp only [Repl.hole, Ty.substPath, Ty.subst, Path.here_ext_subst_one]
theorem ReplDec.hole_open : ∀ {p q : Path s} {D D' : Dec s} (r : ReplDec p q D D') (u : Path s),
    (u = p → r.hole.substPath u = D) ∧ (u = q → r.hole.substPath u = D')
  | _, _, _, _, .rdtyp1 (U := U) r, u => by
      have ih := Repl.hole_open r u
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [ReplDec.hole, Dec.substPath, Dec.subst] <;>
      rw [← Ty.substPath, ← Ty.substPath, Ty.weaken_substPath]
      · rw [ih.1 h]
      · rw [ih.2 h]
  | _, _, _, _, .rdtyp2 (U := U) r, u => by
      have ih := Repl.hole_open r u
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [ReplDec.hole, Dec.substPath, Dec.subst] <;>
      rw [← Ty.substPath, ← Ty.substPath, Ty.weaken_substPath]
      · rw [ih.1 h]
      · rw [ih.2 h]
  | _, _, _, _, .rdtrm r, u => by
      have ih := Repl.hole_open r u
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [ReplDec.hole, Dec.substPath, Dec.subst] <;>
      rw [← Ty.substPath]
      · rw [ih.1 h]
      · rw [ih.2 h]
end

/-- The hole opened at `p` is `T`, opened at `q` it is `T'`. -/
theorem Repl.hole_spec (r : Repl p q T T') : r.hole.substPath p = T ∧ r.hole.substPath q = T' :=
  ⟨(r.hole_open p).1 rfl, (r.hole_open q).2 rfl⟩

/-! ## Lemmas of `Replacement.v` -/

mutual
/-- `repl_swap` (`Replacement.v:19`): if `T[q/p] = T'` then `T'[p/q] = T`. -/
def Repl.swap : Repl p q T T' → Repl q p T' T
  | .rrcd r => .rrcd r.swap
  | .rand1 r => .rand1 r.swap
  | .rand2 r => .rand2 r.swap
  | .rpath => .rpath
  | .rbnd r => .rbnd r.swap
  | .rall1 r => .rall1 r.swap
  | .rall2 r => .rall2 r.swap
  | .rsngl => .rsngl
def ReplDec.swap : ReplDec p q D D' → ReplDec q p D' D
  | .rdtyp1 r => .rdtyp1 r.swap
  | .rdtyp2 r => .rdtyp2 r.swap
  | .rdtrm r => .rdtrm r.swap
end

/-- `repl_intro_sngl` (`Replacement.v:33`): `rsngl` at the empty field list. -/
def repl_intro_sngl (p q : Path s) : Repl p q (.sngl p) (.sngl q) := .rsngl (bs := [])

mutual
/-- `repl_typ_subst` (`Replacement.v:292`), along any path substitution.  Coq substitutes one
variable for another. -/
def Repl.subst {p q : Path s₁} {T T' : Ty s₁} (r : Repl p q T T') (σ : PathSubst s₁ s₂) :
    Repl (p.subst σ) (q.subst σ) (T.subst σ) (T'.subst σ) :=
  match r with
  | .rrcd r => .rrcd (r.subst σ)
  | .rand1 r => .rand1 (r.subst σ)
  | .rand2 r => .rand2 (r.subst σ)
  | .rpath => by
      simp only [Ty.subst, Path.ext_subst]
      exact .rpath
  | .rbnd r => by
      have h := r.subst σ.lift
      rw [Path.weaken_subst_lift, Path.weaken_subst_lift] at h
      exact .rbnd h
  | .rall1 r => .rall1 (r.subst σ)
  | .rall2 r => by
      have h := r.subst σ.lift
      rw [Path.weaken_subst_lift, Path.weaken_subst_lift] at h
      exact .rall2 h
  | .rsngl => by
      simp only [Ty.subst, Path.ext_subst]
      exact .rsngl
def ReplDec.subst {p q : Path s₁} {D D' : Dec s₁} (r : ReplDec p q D D') (σ : PathSubst s₁ s₂) :
    ReplDec (p.subst σ) (q.subst σ) (D.subst σ) (D'.subst σ) :=
  match r with
  | .rdtyp1 r => .rdtyp1 (r.subst σ)
  | .rdtyp2 r => .rdtyp2 (r.subst σ)
  | .rdtrm r => .rdtrm (r.subst σ)
end

/-! ## Deciding replacement

At a selection or a singleton, `Ty.isRepl` strips the prefix `p` from the left path and the prefix `q`
from the right one and compares the two field lists.  At a congruence it asks one side to replace and
the other to be equal. -/

/-- The fields after the prefix `p`: `p.nomDropPrefix l = some bs` exactly when `l = p.nomExt bs`. -/
def _root_.Paths.FCdot.Path.nomDropPrefix (p : Path s) : Path s → Option (List Label)
  | .var y => if Path.var y = p then some [] else none                              -- p.nomDropPrefix y
  | .sel l a => if Path.sel l a = p then some [] else (nomDropPrefix p l).map (· ++ [a])  -- p.nomDropPrefix l.a

/-- `l = p.nomExt bs` and `r = q.nomExt bs` for one field list `bs`. -/
def _root_.Paths.FCdot.Path.nomSameSuffix (p q l r : Path s) : Bool :=
  match p.nomDropPrefix l, q.nomDropPrefix r with
  | some bs, some cs => decide (bs = cs)
  | _, _ => false

mutual
/-- Decides `Repl p q T T'` (`Ty.isRepl_iff`). -/
def Ty.isRepl (p q : Path s) (T T' : Ty s) : Bool :=
  match T, T' with
  | .rcd D, .rcd D' => Dec.isRepl p q D D'                                          -- rrcd
  | .and T U, .and T' U' =>
      (Ty.isRepl p q T T' && decide (U = U')) ||                                    -- rand1
        (decide (T = T') && Ty.isRepl p q U U')                                     -- rand2
  | .sel l A, .sel r A' => decide (A = A') && p.nomSameSuffix q l r                    -- rpath
  | .mu T, .mu T' => Ty.isRepl p.weaken q.weaken T T'                               -- rbnd, under z
  | .all S U, .all S' U' =>
      (Ty.isRepl p q S S' && decide (U = U')) ||                                    -- rall1
        (decide (S = S') && Ty.isRepl p.weaken q.weaken U U')                       -- rall2, under z
  | .sngl l, .sngl r => p.nomSameSuffix q l r                                          -- rsngl
  | _, _ => false
/-- Decides `ReplDec p q D D'` (`Dec.isRepl_iff`). -/
def Dec.isRepl (p q : Path s) (D D' : Dec s) : Bool :=
  match D, D' with
  | .typ A S U, .typ A' S' U' =>
      decide (A = A') &&
        ((Ty.isRepl p q S S' && decide (U = U')) ||                                -- rdtyp1
          (decide (S = S') && Ty.isRepl p q U U'))                                  -- rdtyp2
  | .trm a T, .trm a' T' => decide (a = a') && Ty.isRepl p q T T'                  -- rdtrm
  | _, _ => false
end

theorem Path.ext_append (p : Path s) (bs cs : List Label) : p.nomExt (bs ++ cs) = (p.nomExt bs).nomExt cs := by
  induction bs generalizing p with
  | nil => rfl
  | cons a bs ih => exact ih (p.sel a)

theorem Path.depth_ext (p : Path s) (bs : List Label) : (p.nomExt bs).depth = p.depth + bs.length := by
  induction bs generalizing p with
  | nil => rfl
  | cons a bs ih =>
      rw [Path.nomExt, ih (p.sel a), List.length_cons]
      show p.depth + 1 + bs.length = p.depth + (bs.length + 1)
      omega

theorem Path.dropPrefix_self (p : Path s) : p.nomDropPrefix p = some [] := by
  cases p with
  | var y => exact if_pos rfl
  | sel l a => exact if_pos rfl

/-- Below the prefix, `nomDropPrefix` reads the fields that follow. -/
theorem Path.dropPrefix_ext_of_le (p : Path s) (bs : List Label) :
    ∀ (l : Path s), p.depth ≤ l.depth → p.nomDropPrefix (l.nomExt bs) = (p.nomDropPrefix l).map (· ++ bs) := by
  induction bs with
  | nil =>
      intro l _
      show p.nomDropPrefix l = (p.nomDropPrefix l).map (· ++ [])
      cases p.nomDropPrefix l <;> simp
  | cons a bs ih =>
      intro l hl
      have hne : Path.sel l a ≠ p := fun h => by
        have := congrArg Path.depth h
        simp only [Path.depth] at this
        omega
      have hle : p.depth ≤ (l.sel a).depth := Nat.le_succ_of_le hl
      rw [Path.nomExt, ih (l.sel a) hle]
      show (if Path.sel l a = p then some [] else (p.nomDropPrefix l).map (· ++ [a])).map (· ++ bs)
        = (p.nomDropPrefix l).map (· ++ a :: bs)
      rw [if_neg hne, Option.map_map]
      cases p.nomDropPrefix l <;> simp

theorem Path.dropPrefix_ext (p : Path s) (bs : List Label) : p.nomDropPrefix (p.nomExt bs) = some bs := by
  rw [Path.dropPrefix_ext_of_le p bs p (Nat.le_refl _), Path.dropPrefix_self]
  rfl

theorem Path.eq_ext_of_dropPrefix (p : Path s) :
    ∀ (l : Path s) (bs : List Label), p.nomDropPrefix l = some bs → l = p.nomExt bs
  | .var y, bs, h => by
      by_cases hy : Path.var y = p
      · have h' : some [] = some bs := (if_pos hy).symm.trans h
        cases h'
        exact hy
      · have h' : none = some bs := (if_neg hy).symm.trans h
        cases h'
  | .sel l a, bs, h => by
      by_cases hl : Path.sel l a = p
      · have h' : some [] = some bs := (if_pos hl).symm.trans h
        cases h'
        exact hl
      · have h' : (p.nomDropPrefix l).map (· ++ [a]) = some bs := (if_neg hl).symm.trans h
        cases hd : p.nomDropPrefix l with
        | none =>
            rw [hd] at h'
            cases h'
        | some cs =>
            rw [hd] at h'
            cases h'
            rw [Path.ext_append, Path.eq_ext_of_dropPrefix p l cs hd]
            rfl

theorem Path.sameSuffix_iff (p q l r : Path s) :
    p.nomSameSuffix q l r = true ↔ ∃ bs, l = p.nomExt bs ∧ r = q.nomExt bs := by
  constructor
  · intro h
    unfold Path.nomSameSuffix at h
    cases hl : p.nomDropPrefix l with
    | none =>
        rw [hl] at h
        cases h
    | some bs =>
        cases hr : q.nomDropPrefix r with
        | none =>
            rw [hl, hr] at h
            cases h
        | some cs =>
            rw [hl, hr] at h
            have hbc : bs = cs := of_decide_eq_true h
            subst hbc
            exact ⟨bs, Path.eq_ext_of_dropPrefix p l bs hl, Path.eq_ext_of_dropPrefix q r bs hr⟩
  · rintro ⟨bs, rfl, rfl⟩
    unfold Path.nomSameSuffix
    rw [Path.dropPrefix_ext, Path.dropPrefix_ext]
    exact decide_eq_true rfl

mutual
theorem Ty.isRepl_iff' : ∀ {s : Sig} (p q : Path s) (T T' : Ty s),
    Ty.isRepl p q T T' = true ↔ Nonempty (Repl p q T T')
  | _, _, _, .top, T' => by
      cases T' <;> exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
  | _, _, _, .bot, T' => by
      cases T' <;> exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
  | _, p, q, .rcd D, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i D'
      simp only [Ty.isRepl, Dec.isRepl_iff' p q D D']
      constructor
      · rintro ⟨h⟩
        exact ⟨.rrcd h⟩
      · rintro ⟨h⟩
        cases h with
        | rrcd h => exact ⟨h⟩
  | _, p, q, .and T U, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i T' U'
      simp only [Ty.isRepl, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        Ty.isRepl_iff' p q T T', Ty.isRepl_iff' p q U U']
      constructor
      · rintro (⟨⟨h⟩, rfl⟩ | ⟨rfl, ⟨h⟩⟩)
        · exact ⟨.rand1 h⟩
        · exact ⟨.rand2 h⟩
      · rintro ⟨h⟩
        cases h with
        | rand1 h => exact .inl ⟨⟨h⟩, rfl⟩
        | rand2 h => exact .inr ⟨rfl, ⟨h⟩⟩
  | _, p, q, .sel l A, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i r A'
      simp only [Ty.isRepl, Bool.and_eq_true, decide_eq_true_eq, Path.sameSuffix_iff]
      constructor
      · rintro ⟨rfl, bs, rfl, rfl⟩
        exact ⟨.rpath⟩
      · rintro ⟨h⟩
        cases h with
        | rpath => exact ⟨rfl, _, rfl, rfl⟩
  | _, p, q, .mu T, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i T'
      simp only [Ty.isRepl, Ty.isRepl_iff' p.weaken q.weaken T T']
      constructor
      · rintro ⟨h⟩
        exact ⟨.rbnd h⟩
      · rintro ⟨h⟩
        cases h with
        | rbnd h => exact ⟨h⟩
  | _, p, q, .all S U, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i S' U'
      simp only [Ty.isRepl, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        Ty.isRepl_iff' p q S S', Ty.isRepl_iff' p.weaken q.weaken U U']
      constructor
      · rintro (⟨⟨h⟩, rfl⟩ | ⟨rfl, ⟨h⟩⟩)
        · exact ⟨.rall1 h⟩
        · exact ⟨.rall2 h⟩
      · rintro ⟨h⟩
        cases h with
        | rall1 h => exact .inl ⟨⟨h⟩, rfl⟩
        | rall2 h => exact .inr ⟨rfl, ⟨h⟩⟩
  | _, p, q, .sngl l, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i r
      simp only [Ty.isRepl, Path.sameSuffix_iff]
      constructor
      · rintro ⟨bs, rfl, rfl⟩
        exact ⟨.rsngl⟩
      · rintro ⟨h⟩
        cases h with
        | rsngl => exact ⟨_, rfl, rfl⟩
theorem Dec.isRepl_iff' : ∀ {s : Sig} (p q : Path s) (D D' : Dec s),
    Dec.isRepl p q D D' = true ↔ Nonempty (ReplDec p q D D')
  | _, p, q, .typ A S U, D0 => by
      cases D0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i A' S' U'
      simp only [Dec.isRepl, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        Ty.isRepl_iff' p q S S', Ty.isRepl_iff' p q U U']
      constructor
      · rintro ⟨rfl, (⟨⟨h⟩, rfl⟩ | ⟨rfl, ⟨h⟩⟩)⟩
        · exact ⟨.rdtyp1 h⟩
        · exact ⟨.rdtyp2 h⟩
      · rintro ⟨h⟩
        cases h with
        | rdtyp1 h => exact ⟨rfl, .inl ⟨⟨h⟩, rfl⟩⟩
        | rdtyp2 h => exact ⟨rfl, .inr ⟨rfl, ⟨h⟩⟩⟩
  | _, p, q, .trm a T, D0 => by
      cases D0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun ⟨h⟩ => nomatch h⟩
        | skip
      rename_i a' T'
      simp only [Dec.isRepl, Bool.and_eq_true, decide_eq_true_eq, Ty.isRepl_iff' p q T T']
      constructor
      · rintro ⟨rfl, ⟨h⟩⟩
        exact ⟨.rdtrm h⟩
      · rintro ⟨h⟩
        cases h with
        | rdtrm h => exact ⟨rfl, ⟨h⟩⟩
end

theorem Ty.isRepl_iff : Ty.isRepl p q T T' = true ↔ Nonempty (Repl p q T T') :=
  Ty.isRepl_iff' p q T T'

theorem Dec.isRepl_iff : Dec.isRepl p q D D' = true ↔ Nonempty (ReplDec p q D D') :=
  Dec.isRepl_iff' p q D D'

/-! ## One occurrence at a time

`hole_spec` alone does not pin one occurrence: a hole with two occurrences meets both of its
equations.  The relation does.  At an intersection `rand1` and `rand2` each keep one side unchanged,
so replacing `p` on both sides at once forces `p = q`. -/

theorem repl_one_occurrence {p q : Path s} (hpq : p ≠ q) (a b : Label) :
    ¬ Nonempty (Repl p q (.and (.rcd (.trm a (.sngl p))) (.rcd (.trm b (.sngl p))))
                         (.and (.rcd (.trm a (.sngl q))) (.rcd (.trm b (.sngl q))))) := by
  rintro ⟨r⟩
  cases r with
  | rand1 _ => exact hpq rfl
  | rand2 _ => exact hpq rfl

/-! ## Tight bounds under substitution -/

mutual
theorem Ty.tight_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂),
    T.tight = true → (T.subst σ).tight = true
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .rcd D, σ, h => Dec.tight_subst D σ h
  | .and T U, σ, h => by
      simp only [Ty.tight, Bool.and_eq_true] at h
      simp only [Ty.subst, Ty.tight, Bool.and_eq_true]
      exact ⟨Ty.tight_subst T σ h.1, Ty.tight_subst U σ h.2⟩
  | .sel _ _, _, _ => rfl
  | .mu T, σ, h => Ty.tight_subst T σ.lift h
  | .all _ _, _, _ => rfl
  | .sngl _, _, _ => rfl
theorem Dec.tight_subst : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂),
    D.tight = true → (D.subst σ).tight = true
  | .typ _ T U, σ, h => by
      have hTU : T = U := of_decide_eq_true h
      subst hTU
      exact decide_eq_true rfl
  | .trm _ T, σ, h => Ty.tight_subst T σ h
end

theorem Ty.tight_substPath (T : Ty (s,x)) (p : Path s) : T.tight = true → (T.substPath p).tight = true :=
  Ty.tight_subst T (PathSubst.one p)

/-! ## Tight bounds do not follow from the opened annotation

`ty_def_new` asks for `tight_bounds` of the annotation and, as its third premise, types the
definitions against the annotation opened at the new path.  The witness: the outer self `z`, a field
`b`, the nested self `w`, and the annotation body `{B : ⊤..⊤} ∧ {A : (z.b).B .. w.B}`.  Its bounds
differ, so it is not tight.  Opened at `z.b`, both bounds read `(z.b).B`, so the opened type is tight. -/

/-- The field `b`. -/
abbrev tightEx_b : Label := .trm 0
/-- The type member `A`. -/
abbrev tightEx_A : Label := .typ 0
/-- The type member `B`. -/
abbrev tightEx_B : Label := .typ 1

/-- `{B : ⊤..⊤} ∧ {A : (z.b).B .. w.B}` over `(([], z), w)`: `z` is `.there .here`, `w` is `.here`. -/
abbrev tightEx_T : Ty (([],x),x) :=
  .and (.rcd (.typ tightEx_B .top .top))
    (.rcd (.typ tightEx_A (.sel (.sel (.var (.there .here)) tightEx_b) tightEx_B)
      (.sel (.var .here) tightEx_B)))

/-- `z.b` over `([], z)`: `z` is `.here`. -/
abbrev tightEx_r : Path ([],x) := .sel (.var .here) tightEx_b

theorem tight_premise_independent :
    ∃ (T : Ty (([],x),x)) (r : Path ([],x)), (Ty.mu T).tight = false ∧ (T.substPath r).tight = true :=
  ⟨tightEx_T, tightEx_r, by decide, by decide⟩

end Nominal.Source
