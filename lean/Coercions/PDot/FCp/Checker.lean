import Coercions.PDot.FCp.Typing

/-!
# FCp checker (plan T.8)

Every rule of T.3 is syntax directed given its annotations (`plan-10-pdot.md:701-705`).  So each
judgment of the evidence block and the terms synthesizes its outputs from its subject, and the
definitions of a literal are checked against their telescope.  The side conditions are syntactic
equalities, label lists and `Γ.defAt`.  The checker never computes `canon`, `res` or `norm`.

Three functions read back what a rule builds.  `Telescope.get?` reads the proposition at a
position, the function behind `Telescope.At`.  `Ty.unweaken` and `Path.unweaken` recover `T` from
`T↑`, through a partial renaming that inverts `Rename.succ`.  `LE-Bound` and `TM-Let` read their
type through `Ty.unweaken`, and `DF-Path` reads the path of its singleton through `Path.unweaken`.

The sides of a template are read in one direction each.  `synthPre sd X` is the `S` of
`sd : S ≤ X` and `synthPost sd Y` is the `T` of `sd : Y ≤ T`, as `MO-Le` and `MO-Fld` ask them.

Every function is structural.  The mutual recursion follows the evidence or the term, and the
context is an argument that changes.  Soundness is one structural recursion on the subject of each
function, in this module.  Completeness is `CheckerCompleteness.lean`.

Each case of a checker function carries the name of the rule it reads in a comment.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Reading a telescope -/

def Telescope.get? : Telescope s → Nat → Option (Pr s)
  | .nil, _ => none
  | .cons Tel pr, i => if i = Tel.length then some pr else Tel.get? i

/-- A position of a telescope is below its length. -/
theorem Telescope.At.lt_length {Tel : Telescope s} {i : Nat} {pr : Pr s} (h : Tel.At i pr) : i < Tel.length := by
  induction h with
  | here => exact Nat.lt_succ_self _
  | there _ ih => exact Nat.lt_succ_of_lt ih

theorem Telescope.get?_iff {Tel : Telescope s} {i : Nat} {pr : Pr s} : Tel.get? i = some pr ↔ Tel.At i pr :=
  match Tel with
  | .nil => ⟨fun h => (nomatch h), fun h => (Telescope.At.nil_of_eq h rfl).elim⟩
  | .cons Tel pr₀ => by
      rw [Telescope.At.cons_iff]
      show (if i = Tel.length then some pr₀ else Tel.get? i) = some pr ↔ _
      by_cases hi : i = Tel.length
      · rw [if_pos hi]
        constructor
        · intro h
          cases h
          exact Or.inl ⟨hi, rfl⟩
        · intro h
          rcases h with ⟨_, rfl⟩ | h
          · rfl
          · subst hi
            exact absurd h.lt_length (Nat.lt_irrefl _)
      · rw [if_neg hi, Telescope.get?_iff]
        constructor
        · exact Or.inr
        · intro h
          rcases h with ⟨h, _⟩ | h
          · exact absurd h hi
          · exact h

/-! ## Reading back a weakening -/

/-- A partial renaming: each variable to a variable, or to nothing. -/
def PRename (s₁ s₂ : Sig) : Type := BVar s₁ .var → Option (BVar s₂ .var)

/-- Under one binder the new binder reads itself. -/
def PRename.lift (f : PRename s₁ s₂) : PRename (s₁,x) (s₂,x) := fun
  | .here => some .here
  | .there y => (f y).map .there

/-- The partial inverse of `Rename.succ`: the newest binder has no image. -/
def PRename.unsucc : PRename (s,x) s := fun
  | .here => none
  | .there y => some y

def Path.unrename : Path s₁ → PRename s₁ s₂ → Option (Path s₂)
  | .var y, f => (f y).map .var
  | .sel p a, f => (Path.unrename p f).map (.sel · a)

mutual
def Ty.unrename : Ty s₁ → PRename s₁ s₂ → Option (Ty s₂)
  | .bot, _ => some .bot
  | .sel p A, f => (Path.unrename p f).map (.sel · A)
  | .pi S T, f => match S.unrename f, T.unrename f.lift with                -- under z of Π(z : S) T
    | some S', some T' => some (.pi S' T')
    | _, _ => none
  | .mu Tel, f => (Tel.unrename f.lift).map .mu                             -- under w of μ(w : Tel)
def Pr.unrename : Pr s₁ → PRename s₁ s₂ → Option (Pr s₂)
  | .le S T, f => match S.unrename f, T.unrename f with
    | some S', some T' => some (.le S' T')
    | _, _ => none
  | .fld a T, f => (T.unrename f).map (.fld a)
  | .alias q, f => (Path.unrename q f).map .alias
  | .is T, f => (T.unrename f).map .is
def Telescope.unrename : Telescope s₁ → PRename s₁ s₂ → Option (Telescope s₂)
  | .nil, _ => some .nil
  | .cons Tel pr, f => match Tel.unrename f, pr.unrename f with
    | some Tel', some pr' => some (.cons Tel' pr')
    | _, _ => none
end

def Ty.unweaken : Ty (s,x) → Option (Ty s)                  -- the T with T↑ = U, if any
  | U => U.unrename PRename.unsucc
def Path.unweaken : Path (s,x) → Option (Path s)            -- the q with q↑ = p, if any, called as Path.unweaken p
  | p => Path.unrename p PRename.unsucc

/-- `f` reads back `ρ`: each variable `ρ y` to `y`, and no other variable to anything. -/
structure PRename.Inverts (f : PRename s₁ s₂) (ρ : Rename s₂ s₁) : Prop where
  back : ∀ y, f (ρ.var y) = some y
  image : ∀ x y, f x = some y → x = ρ.var y

theorem PRename.Inverts.lift {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) : f.lift.Inverts ρ.lift where
  back := fun
    | .here => rfl
    | .there y => by
        show (f (ρ.var y)).map BVar.there = some (BVar.there y)
        rw [h.back y]
        rfl
  image := fun
    | .here, _, e => by
        cases e
        rfl
    | .there x, _, e => by
        obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 e
        exact congrArg BVar.there (h.image x z hz)

theorem PRename.unsucc_inverts : (PRename.unsucc : PRename (s,x) s).Inverts Rename.succ where
  back := fun _ => rfl
  image := fun
    | .here, _, e => by cases e
    | .there _, _, e => by
        cases e
        rfl

theorem Path.unrename_rename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (p : Path s₂), Path.unrename (p.rename ρ) f = some p
  | .var y => by
      show (f (ρ.var y)).map Path.var = some (Path.var y)
      rw [h.back y]
      rfl
  | .sel p a => by
      show (Path.unrename (p.rename ρ) f).map (Path.sel · a) = some (Path.sel p a)
      rw [Path.unrename_rename h p]
      rfl

theorem Path.eq_rename_of_unrename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (p : Path s₁) (q : Path s₂), Path.unrename p f = some q → p = q.rename ρ
  | .var y, _, e => by
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg Path.var (h.image y z hz)
  | .sel p a, _, e => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg (Path.sel · a) (Path.eq_rename_of_unrename h p q hq)

mutual
theorem Ty.unrename_rename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (T : Ty s₂), (T.rename ρ).unrename f = some T
  | .bot => rfl
  | .sel p A => by
      show (Path.unrename (p.rename ρ) f).map (Ty.sel · A) = some (Ty.sel p A)
      rw [Path.unrename_rename h p]
      rfl
  | .pi S T => by
      simp only [Ty.rename, Ty.unrename, Ty.unrename_rename h S, Ty.unrename_rename h.lift T]
  | .mu Tel => by
      simp only [Ty.rename, Ty.unrename, Telescope.unrename_rename h.lift Tel]
      rfl
theorem Pr.unrename_rename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (pr : Pr s₂), (pr.rename ρ).unrename f = some pr
  | .le S T => by
      simp only [Pr.rename, Pr.unrename, Ty.unrename_rename h S, Ty.unrename_rename h T]
  | .fld a T => by
      simp only [Pr.rename, Pr.unrename, Ty.unrename_rename h T]
      rfl
  | .alias q => by
      simp only [Pr.rename, Pr.unrename, Path.unrename_rename h q]
      rfl
  | .is T => by
      simp only [Pr.rename, Pr.unrename, Ty.unrename_rename h T]
      rfl
theorem Telescope.unrename_rename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (Tel : Telescope s₂), (Tel.rename ρ).unrename f = some Tel
  | .nil => rfl
  | .cons Tel pr => by
      simp only [Telescope.rename, Telescope.unrename, Telescope.unrename_rename h Tel, Pr.unrename_rename h pr]
end

mutual
theorem Ty.eq_rename_of_unrename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (T : Ty s₁) (U : Ty s₂), T.unrename f = some U → T = U.rename ρ
  | .bot, _, e => by
      cases e
      rfl
  | .sel p A, _, e => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg (Ty.sel · A) (Path.eq_rename_of_unrename h p q hq)
  | .pi S T, _, e => by
      simp only [Ty.unrename] at e
      split at e
      next S' T' hS hT =>
        cases e
        rw [Ty.eq_rename_of_unrename h S S' hS, Ty.eq_rename_of_unrename h.lift T T' hT]
        rfl
      next => cases e
  | .mu Tel, _, e => by
      obtain ⟨Tel', hT, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg Ty.mu (Telescope.eq_rename_of_unrename h.lift Tel Tel' hT)
theorem Pr.eq_rename_of_unrename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (pr : Pr s₁) (pr' : Pr s₂), pr.unrename f = some pr' → pr = pr'.rename ρ
  | .le S T, _, e => by
      simp only [Pr.unrename] at e
      split at e
      next S' T' hS hT =>
        cases e
        rw [Ty.eq_rename_of_unrename h S S' hS, Ty.eq_rename_of_unrename h T T' hT]
        rfl
      next => cases e
  | .fld a T, _, e => by
      obtain ⟨T', hT, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg (Pr.fld a) (Ty.eq_rename_of_unrename h T T' hT)
  | .alias q, _, e => by
      obtain ⟨q', hq, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg Pr.alias (Path.eq_rename_of_unrename h q q' hq)
  | .is T, _, e => by
      obtain ⟨T', hT, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg Pr.is (Ty.eq_rename_of_unrename h T T' hT)
theorem Telescope.eq_rename_of_unrename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (Tel : Telescope s₁) (Tel' : Telescope s₂), Tel.unrename f = some Tel' → Tel = Tel'.rename ρ
  | .nil, _, e => by
      cases e
      rfl
  | .cons Tel pr, _, e => by
      simp only [Telescope.unrename] at e
      split at e
      next Tel₀ pr₀ hT hp =>
        cases e
        rw [Telescope.eq_rename_of_unrename h Tel Tel₀ hT, Pr.eq_rename_of_unrename h pr pr₀ hp]
        rfl
      next => cases e
end

theorem Ty.unweaken_iff {T : Ty (s,x)} {U : Ty s} : T.unweaken = some U ↔ T = U.weaken :=
  ⟨Ty.eq_rename_of_unrename PRename.unsucc_inverts T U, fun e => e ▸ Ty.unrename_rename PRename.unsucc_inverts U⟩
theorem Path.unweaken_iff {p : Path (s,x)} {q : Path s} : Path.unweaken p = some q ↔ p = q.weaken :=
  ⟨Path.eq_rename_of_unrename PRename.unsucc_inverts p q, fun e => e ▸ Path.unrename_rename PRename.unsucc_inverts q⟩

/-! ## The checker -/

mutual
def synthPEq (Γ : Ctx s) : PEq s → Option (Path s × Path s)
  | .refl p => some (p, p)                                                  -- PE-Refl
  | .symm π => match synthPEq Γ π with                                      -- PE-Symm
    | some (p, q) => some (q, p)
    | none => none
  | .trans π π' => match synthPEq Γ π, synthPEq Γ π' with                   -- PE-Trans
    | some (p, q), some (q', r) => if q = q' then some (p, r) else none
    | _, _ => none
  | .sel π a => match synthPEq Γ π with                                     -- PE-Sel
    | some (p, q) => some (.sel p a, .sel q a)
    | none => none
  | .member P e i => match synthPath Γ P, synthLe Γ e with                  -- PE-Member
    | some S, some (S', .mu Tel) =>
      if S = S' then
        match Tel.get? i with
        | some (.alias q) => some (P.path, q.substPath P.path)
        | _ => none
      else none
    | _, _ => none
def synthPath (Γ : Ctx s) : PathCo s → Option (Ty s)
  | .var x => some (Γ.ty x)                                                 -- PA-Var
  | .sel P a i => match synthPath Γ P with                                  -- PA-Sel
    | some (.mu Tel) =>
      match Tel.get? i with
      | some (.fld a' T) => if a = a' then some (T.substPath P.path) else none
      | _ => none
    | _ => none
  | .cast P e => match synthPath Γ P, synthLe Γ e with                      -- PA-Cast
    | some S, some (S', T) => if S = S' then some T else none
    | _, _ => none
  | .alias P₀ π Q => match synthPath Γ P₀, synthPEq Γ π, synthPath Γ Q with -- PA-Alias
    | some _, some (p, q), some T => if p = P₀.path ∧ q = Q.path then some T else none
    | _, _, _ => none
  | .sngl P q π => match synthPath Γ P, synthPEq Γ π with                   -- PA-Sngl
    | some _, some (p, q') => if p = P.path ∧ q' = q then some (Ty.sngl q) else none
    | _, _ => none
  | .fldI p a Q => match synthPath Γ Q with                                 -- PA-FldI
    | some T => if Q.path = .sel p a then some (.mu (.cons .nil (.fld a T.weaken))) else none
    | none => none
  | .fold Tel P => match synthPath Γ P with                                 -- PA-Fold
    | some T => if T = .mu (Tel.substPath P.path).weaken then some (.mu Tel) else none
    | none => none
  | .unfold P => match synthPath Γ P with                                   -- PA-Unfold
    | some (.mu Tel) => some (.mu (Tel.substPath P.path).weaken)
    | _ => none
  | .both Tel Tel' P Q => match synthPath Γ P, synthPath Γ Q with           -- PA-Both
    | some T, some T' =>
      if T = .mu Tel ∧ T' = .mu Tel' ∧ Q.path = P.path then some (.mu (Tel ++ Tel')) else none
    | _, _ => none
def synthLe (Γ : Ctx s) : LeCo s → Option (Ty s × Ty s)
  | .refl T => some (T, T)                                                  -- LE-Refl
  | .trans e f => match synthLe Γ e, synthLe Γ f with                       -- LE-Trans
    | some (S, M), some (M', T) => if M = M' then some (S, T) else none
    | _, _ => none
  | .top T => some (T, .top)                                                -- LE-Top
  | .bot T => some (.bot, T)                                                -- LE-Bot
  | .eqToLe φ => synthEq Γ φ                                                -- LE-Eq
  | .pi e f => match synthLe Γ e with                                       -- LE-Pi
    | some (S₂, S₁) =>
      match synthLe (Γ.cons (.opaque S₂)) f with                            -- f under z : S₂
      | some (T₁, T₂) => some (.pi S₁ T₁, .pi S₂ T₂)
      | none => none
    | none => none
  | .obj Tel m => match synthMor Γ Tel m with                               -- LE-Obj
    | some Tel' => some (.mu Tel, .mu Tel')
    | none => none
  | .pair Tel Tel' e f => match synthLe Γ e, synthLe Γ f with               -- LE-Pair
    | some (S, T), some (S', T') =>
      if S' = S ∧ T = .mu Tel ∧ T' = .mu Tel' then some (S, .mu (Tel ++ Tel')) else none
    | _, _ => none
  | .bound Tel i => match Tel.get? i with                                   -- LE-Bound
    | some (.is T') =>
      match T'.unweaken with
      | some T => some (.mu Tel, T)
      | none => none
    | _ => none
  | .intoBnd e => match synthLe Γ e with                                    -- LE-IntoBnd
    | some (S, T) => some (S, .mu (.cons .nil (.is T.weaken)))
    | none => none
  | .member P e i => match synthPath Γ P, synthLe Γ e with                  -- LE-Member
    | some S, some (S', .mu Tel) =>
      if S = S' then
        match Tel.get? i with
        | some (.le S₁ T₁) => some (S₁.substPath P.path, T₁.substPath P.path)
        | _ => none
      else none
    | _, _ => none
def synthEq (Γ : Ctx s) : EqCo s → Option (Ty s × Ty s)
  | .refl T => some (T, T)                                                  -- EQ-Refl
  | .symm φ => match synthEq Γ φ with                                       -- EQ-Symm
    | some (S, T) => some (T, S)
    | none => none
  | .trans φ ψ => match synthEq Γ φ, synthEq Γ ψ with                       -- EQ-Trans
    | some (S, M), some (M', T) => if M = M' then some (S, T) else none
    | _, _ => none
  | .defP p A => match Γ.defAt p A with                                     -- EQ-Def
    | some W => some (.sel p A, W)
    | none => none
  | .lift T π => match synthPEq Γ π with                                    -- EQ-Lift
    | some (p, q) => some (T.substPath p, T.substPath q)
    | none => none
  | .dom φ => match synthEq Γ φ with                                        -- EQ-Dom
    | some (.pi S₁ _, .pi S₂ _) => some (S₁, S₂)
    | _ => none
  | .cod φ p => match synthEq Γ φ with                                      -- EQ-Cod
    | some (.pi _ T₁, .pi _ T₂) => some (T₁.substPath p, T₂.substPath p)
    | _ => none
def synthMor (Γ : Ctx s) (src : Telescope (s,x)) : Morphism s → Option (Telescope (s,x))
  | .nil => some .nil                                                       -- MO-Nil
  | .le m pre j post => match synthMor Γ src m, src.get? j with             -- MO-Le
    | some Tel, some (.le X Y) =>
      match synthPre Γ pre X, synthPost Γ post Y with
      | some S, some T => some (.cons Tel (.le S T))
      | _, _ => none
    | _, _ => none
  | .fld m j sd => match synthMor Γ src m, src.get? j with                  -- MO-Fld
    | some Tel, some (.fld a X) =>
      match synthPost Γ sd X with
      | some T => some (.cons Tel (.fld a T))
      | none => none
    | _, _ => none
  | .alias m j => match synthMor Γ src m, src.get? j with                   -- MO-Alias
    | some Tel, some (.alias q) => some (.cons Tel (.alias q))
    | _, _ => none
  | .is m e => match synthMor Γ src m, synthLe Γ e with                     -- MO-Is
    | some Tel, some (S, T) => if S = .mu src then some (.cons Tel (.is T.weaken)) else none
    | _, _ => none
def synthPre (Γ : Ctx s) : Side s → Ty (s,x) → Option (Ty (s,x))      -- the S of sd : S ≤ X, from X
  | .none, X => some X                                                      -- SD-None
  | .some e, X => match synthLe Γ e with                                    -- SD-Some
    | some (S, T) => if T.weaken = X then some S.weaken else none
    | none => none
  | .bot X', X => if X' = X then some .bot else none                        -- SD-Bot
  | .top X', X => if X = .top then some X' else none                        -- SD-Top
def synthPost (Γ : Ctx s) : Side s → Ty (s,x) → Option (Ty (s,x))     -- the T of sd : Y ≤ T, from Y
  | .none, Y => some Y                                                      -- SD-None
  | .some e, Y => match synthLe Γ e with                                    -- SD-Some
    | some (S, T) => if S.weaken = Y then some T.weaken else none
    | none => none
  | .bot X', Y => if Y = .bot then some X' else none                        -- SD-Bot
  | .top X', Y => if X' = Y then some .top else none                        -- SD-Top
end
mutual
def synthTm (Γ : Ctx s) : Tm s → Option (Ty s)
  | .path P => synthPath Γ P                                                -- TM-Path
  | .val v => synthValue Γ v                                                -- TM-Val
  | .app P Q => match synthPath Γ P, synthPath Γ Q with                     -- TM-App
    | some (.pi S T), some S' => if S' = S then some (T.substPath Q.path) else none
    | _, _ => none
  | .lett t u => match synthTm Γ t with                                     -- TM-Let
    | some T =>
      match synthTm (Γ.cons (.opaque T)) u with                             -- u under z : T
      | some U => U.unweaken
      | none => none
    | none => none
  | .cast t e => match synthTm Γ t, synthLe Γ e with                        -- TM-Cast
    | some S, some (S', T) => if S = S' then some T else none
    | _, _ => none
def synthValue (Γ : Ctx s) : Value s → Option (Ty s)
  | .lam S t => match synthTm (Γ.cons (.opaque S)) t with                   -- VA-Lam, t under z : S
    | some T => some (.pi S T)
    | none => none
  | .obj Tel ds =>                                                          -- VA-Obj, ds under the self z
    if checkDefs (Γ.cons (.transparent (.mu Tel) ds.block)) (.var .here) ds (Tel.rename Rename.succ.lift)
    then some (.mu Tel) else none
  | .cast v e => match synthValue Γ v, synthLe Γ e with                     -- VA-Cast
    | some S, some (S', T) => if S = S' then some T else none
    | _, _ => none
def checkDefs (Γ : Ctx s) (p : Path s) : Defs s → Telescope (s,x) → Bool
  | .nil, Tel => match Tel with                                             -- DF-Nil
    | .nil => true
    | _ => false
  | .typ ds A U, Tel => match Tel with                                      -- DF-Typ
    | .cons (.cons Tel (.le W X)) (.le X' W') =>
      decide (X = .sel (.var .here) A ∧ X' = .sel (.var .here) A ∧ W' = W ∧ A ∉ ds.labels ∧ U = W.substPath p) &&
        checkDefs Γ p ds Tel
    | _ => false
  | .fld ds a (.path P), Tel => match Tel with                              -- DF-Path
    | .cons Tel (.fld a' (.mu (.cons .nil (.alias q')))) =>
      match Path.unweaken q', synthPath Γ P with
      | some q, some _ => decide (a' = a ∧ a ∉ ds.labels ∧ P.path = q.substPath p) && checkDefs Γ p ds Tel
      | _, _ => false
    | _ => false
  | .fld ds a (.fn v), Tel => match Tel with                                -- DF-Fun
    | .cons Tel (.fld a' (.pi S T)) =>
      decide (a' = a ∧ a ∉ ds.labels ∧ v.isLam = true) &&
        decide (synthValue Γ v = some ((Ty.pi S T).substPath p)) && checkDefs Γ p ds Tel
    | _ => false
  | .fld ds a (.nest Tel'' ds'), Tel => match Tel with                      -- DF-Nest
    | .cons Tel (.fld a' (.mu Tel')) =>
      decide (a' = a ∧ a ∉ ds.labels ∧ Tel'' = Tel'.subst (PathSubst.one p).lift) &&
        checkDefs Γ (.sel p a) ds' Tel'' && checkDefs Γ p ds Tel
    | _ => false
end
def checkTm (Γ : Ctx s) (t : Tm s) (T : Ty s) : Bool := decide (synthTm Γ t = some T)
def checkPath (Γ : Ctx s) (P : PathCo s) (T : Ty s) : Bool := decide (synthPath Γ P = some T)

/-! ## Soundness

One structural recursion on the subject of each function.  Each case unfolds one step of the
function, splits on the results of the recursive calls and on its side conditions, and builds the
rule of T.3 that the case reads. -/

mutual
theorem synthPEq_sound {Γ : Ctx s} {π : PEq s} {p q : Path s} : synthPEq Γ π = some (p, q) → PEq.HasType Γ π p q :=
  match π with
  | .refl r => fun h => by
      simp only [synthPEq] at h
      cases h
      exact .refl
  | .symm π => fun h => by
      simp only [synthPEq] at h
      split at h
      next p' q' hπ =>
        cases h
        exact .symm (synthPEq_sound hπ)
      next => cases h
  | .trans π π' => fun h => by
      simp only [synthPEq] at h
      split at h
      next p' q' q'' r hπ hπ' =>
        split at h
        next hq =>
          cases h
          subst hq
          exact .trans (synthPEq_sound hπ) (synthPEq_sound hπ')
        next => cases h
      next => cases h
  | .sel π a => fun h => by
      simp only [synthPEq] at h
      split at h
      next p' q' hπ =>
        cases h
        exact .sel (synthPEq_sound hπ)
      next => cases h
  | .member P e i => fun h => by
      simp only [synthPEq] at h
      split at h
      next S S' Tel hP he =>
        split at h
        next hS =>
          subst hS
          split at h
          next q' hi =>
            cases h
            exact .member (synthPath_sound hP) (synthLe_sound he) (Telescope.get?_iff.1 hi)
          next => cases h
        next => cases h
      next => cases h
theorem synthPath_sound {Γ : Ctx s} {P : PathCo s} {T : Ty s} : synthPath Γ P = some T → PathCo.HasType Γ P T :=
  match P with
  | .var y => fun h => by
      simp only [synthPath] at h
      cases h
      exact .var rfl
  | .sel P a i => fun h => by
      simp only [synthPath] at h
      split at h
      next Tel hP =>
        split at h
        next a' T' hi =>
          split at h
          next ha =>
            subst ha
            cases h
            exact .sel (synthPath_sound hP) (Telescope.get?_iff.1 hi)
          next => cases h
        next => cases h
      next => cases h
  | .cast P e => fun h => by
      simp only [synthPath] at h
      split at h
      next S S' T' hP he =>
        split at h
        next hS =>
          subst hS
          cases h
          exact .cast (synthPath_sound hP) (synthLe_sound he)
        next => cases h
      next => cases h
  | .alias P₀ π Q => fun h => by
      simp only [synthPath] at h
      split at h
      next S p' q' T' hP₀ hπ hQ =>
        split at h
        next hpq =>
          obtain ⟨rfl, rfl⟩ := hpq
          cases h
          exact .alias (synthPath_sound hP₀) (synthPEq_sound hπ) (synthPath_sound hQ)
        next => cases h
      next => cases h
  | .sngl P q π => fun h => by
      simp only [synthPath] at h
      split at h
      next S p' q' hP hπ =>
        split at h
        next hpq =>
          obtain ⟨rfl, rfl⟩ := hpq
          cases h
          exact .sngl (synthPath_sound hP) (synthPEq_sound hπ)
        next => cases h
      next => cases h
  | .fldI p a Q => fun h => by
      simp only [synthPath] at h
      split at h
      next T' hQ =>
        split at h
        next hp =>
          cases h
          exact .fldI (synthPath_sound hQ) hp
        next => cases h
      next => cases h
  | .fold Tel P => fun h => by
      simp only [synthPath] at h
      split at h
      next T' hP =>
        split at h
        next hT =>
          subst hT
          cases h
          exact .fold (synthPath_sound hP)
        next => cases h
      next => cases h
  | .unfold P => fun h => by
      simp only [synthPath] at h
      split at h
      next Tel hP =>
        cases h
        exact .unfold (synthPath_sound hP)
      next => cases h
  | .both Tel Tel' P Q => fun h => by
      simp only [synthPath] at h
      split at h
      next T₁ T₂ hP hQ =>
        split at h
        next hT =>
          obtain ⟨rfl, rfl, hpath⟩ := hT
          cases h
          exact .both (synthPath_sound hP) (synthPath_sound hQ) hpath
        next => cases h
      next => cases h
theorem synthLe_sound {Γ : Ctx s} {e : LeCo s} {S T : Ty s} : synthLe Γ e = some (S, T) → LeCo.HasType Γ e S T :=
  match e with
  | .refl U => fun h => by
      simp only [synthLe] at h
      cases h
      exact .refl
  | .trans e f => fun h => by
      simp only [synthLe] at h
      split at h
      next S' M M' T' he hf =>
        split at h
        next hM =>
          subst hM
          cases h
          exact .trans (synthLe_sound he) (synthLe_sound hf)
        next => cases h
      next => cases h
  | .top U => fun h => by
      simp only [synthLe] at h
      cases h
      exact .top
  | .bot U => fun h => by
      simp only [synthLe] at h
      cases h
      exact .bot
  | .eqToLe φ => fun h => by
      simp only [synthLe] at h
      exact .eqToLe (synthEq_sound h)
  | .pi e f => fun h => by
      simp only [synthLe] at h
      split at h
      next S₂ S₁ he =>
        split at h
        next T₁ T₂ hf =>
          cases h
          exact .pi (synthLe_sound he) (synthLe_sound hf)
        next => cases h
      next => cases h
  | .obj Tel m => fun h => by
      simp only [synthLe] at h
      split at h
      next Tel' hm =>
        cases h
        exact .obj (synthMor_sound hm)
      next => cases h
  | .pair Tel Tel' e f => fun h => by
      simp only [synthLe] at h
      split at h
      next S₁ T₁ S₂ T₂ he hf =>
        split at h
        next hT =>
          obtain ⟨rfl, rfl, rfl⟩ := hT
          cases h
          exact .pair (synthLe_sound he) (synthLe_sound hf)
        next => cases h
      next => cases h
  | .bound Tel i => fun h => by
      simp only [synthLe] at h
      split at h
      next T' hi =>
        split at h
        next U hU =>
          cases h
          rw [Ty.unweaken_iff] at hU
          subst hU
          exact .bound (Telescope.get?_iff.1 hi)
        next => cases h
      next => cases h
  | .intoBnd e => fun h => by
      simp only [synthLe] at h
      split at h
      next S' T' he =>
        cases h
        exact .intoBnd (synthLe_sound he)
      next => cases h
  | .member P e i => fun h => by
      simp only [synthLe] at h
      split at h
      next S₀ S₀' Tel hP he =>
        split at h
        next hS =>
          subst hS
          split at h
          next S₁ T₁ hi =>
            cases h
            exact .member (synthPath_sound hP) (synthLe_sound he) (Telescope.get?_iff.1 hi)
          next => cases h
        next => cases h
      next => cases h
theorem synthEq_sound {Γ : Ctx s} {φ : EqCo s} {S T : Ty s} : synthEq Γ φ = some (S, T) → EqCo.HasType Γ φ S T :=
  match φ with
  | .refl U => fun h => by
      simp only [synthEq] at h
      cases h
      exact .refl
  | .symm φ => fun h => by
      simp only [synthEq] at h
      split at h
      next S' T' hφ =>
        cases h
        exact .symm (synthEq_sound hφ)
      next => cases h
  | .trans φ ψ => fun h => by
      simp only [synthEq] at h
      split at h
      next S' M M' T' hφ hψ =>
        split at h
        next hM =>
          subst hM
          cases h
          exact .trans (synthEq_sound hφ) (synthEq_sound hψ)
        next => cases h
      next => cases h
  | .defP p A => fun h => by
      simp only [synthEq] at h
      split at h
      next W hW =>
        cases h
        exact .defP hW
      next => cases h
  | .lift U π => fun h => by
      simp only [synthEq] at h
      split at h
      next p q hπ =>
        cases h
        exact .lift (synthPEq_sound hπ)
      next => cases h
  | .dom φ => fun h => by
      simp only [synthEq] at h
      split at h
      next S₁ T₁ S₂ T₂ hφ =>
        cases h
        exact .dom (synthEq_sound hφ)
      next => cases h
  | .cod φ p => fun h => by
      simp only [synthEq] at h
      split at h
      next S₁ T₁ S₂ T₂ hφ =>
        cases h
        exact .cod (synthEq_sound hφ)
      next => cases h
theorem synthMor_sound {Γ : Ctx s} {src Tel : Telescope (s,x)} {m : Morphism s} : synthMor Γ src m = some Tel → Morphism.HasType Γ src m Tel :=
  match m with
  | .nil => fun h => by
      simp only [synthMor] at h
      cases h
      exact .nil
  | .le m pre j post => fun h => by
      simp only [synthMor] at h
      split at h
      next Tel' X Y hm hj =>
        split at h
        next S' T' hpre hpost =>
          cases h
          exact .le (synthMor_sound hm) (Telescope.get?_iff.1 hj) (synthPre_sound hpre) (synthPost_sound hpost)
        next => cases h
      next => cases h
  | .fld m j sd => fun h => by
      simp only [synthMor] at h
      split at h
      next Tel' a X hm hj =>
        split at h
        next T' hsd =>
          cases h
          exact .fld (synthMor_sound hm) (Telescope.get?_iff.1 hj) (synthPost_sound hsd)
        next => cases h
      next => cases h
  | .alias m j => fun h => by
      simp only [synthMor] at h
      split at h
      next Tel' q hm hj =>
        cases h
        exact .alias (synthMor_sound hm) (Telescope.get?_iff.1 hj)
      next => cases h
  | .is m e => fun h => by
      simp only [synthMor] at h
      split at h
      next Tel' S' T' hm he =>
        split at h
        next hS =>
          subst hS
          cases h
          exact .is (synthMor_sound hm) (synthLe_sound he)
        next => cases h
      next => cases h
theorem synthPre_sound {Γ : Ctx s} {sd : Side s} {S X : Ty (s,x)} : synthPre Γ sd X = some S → Side.HasType Γ sd S X :=
  match sd with
  | .none => fun h => by
      simp only [synthPre] at h
      cases h
      exact .none
  | .some e => fun h => by
      simp only [synthPre] at h
      split at h
      next S' T' he =>
        split at h
        next hX =>
          subst hX
          cases h
          exact .some (synthLe_sound he)
        next => cases h
      next => cases h
  | .bot X' => fun h => by
      simp only [synthPre] at h
      split at h
      next hX =>
        subst hX
        cases h
        exact .bot
      next => cases h
  | .top X' => fun h => by
      simp only [synthPre] at h
      split at h
      next hX =>
        subst hX
        cases h
        exact .top
      next => cases h
theorem synthPost_sound {Γ : Ctx s} {sd : Side s} {Y T : Ty (s,x)} : synthPost Γ sd Y = some T → Side.HasType Γ sd Y T :=
  match sd with
  | .none => fun h => by
      simp only [synthPost] at h
      cases h
      exact .none
  | .some e => fun h => by
      simp only [synthPost] at h
      split at h
      next S' T' he =>
        split at h
        next hY =>
          subst hY
          cases h
          exact .some (synthLe_sound he)
        next => cases h
      next => cases h
  | .bot X' => fun h => by
      simp only [synthPost] at h
      split at h
      next hY =>
        subst hY
        cases h
        exact .bot
      next => cases h
  | .top X' => fun h => by
      simp only [synthPost] at h
      split at h
      next hY =>
        subst hY
        cases h
        exact .top
      next => cases h
end

mutual
theorem synthTm_sound {Γ : Ctx s} {t : Tm s} {T : Ty s} : synthTm Γ t = some T → Tm.HasType Γ t T :=
  match t with
  | .path P => fun h => by
      simp only [synthTm] at h
      exact .path (synthPath_sound h)
  | .val v => fun h => by
      simp only [synthTm] at h
      exact .val (synthValue_sound h)
  | .app P Q => fun h => by
      simp only [synthTm] at h
      split at h
      next S T' S' hP hQ =>
        split at h
        next hS =>
          subst hS
          cases h
          exact .app (synthPath_sound hP) (synthPath_sound hQ)
        next => cases h
      next => cases h
  | .lett t u => fun h => by
      simp only [synthTm] at h
      split at h
      next T' ht =>
        split at h
        next U hu =>
          rw [Ty.unweaken_iff] at h
          subst h
          exact .lett (synthTm_sound ht) (synthTm_sound hu)
        next => cases h
      next => cases h
  | .cast t e => fun h => by
      simp only [synthTm] at h
      split at h
      next S S' T' ht he =>
        split at h
        next hS =>
          subst hS
          cases h
          exact .cast (synthTm_sound ht) (synthLe_sound he)
        next => cases h
      next => cases h
theorem synthValue_sound {Γ : Ctx s} {v : Value s} {T : Ty s} : synthValue Γ v = some T → Value.HasType Γ v T :=
  match v with
  | .lam S t => fun h => by
      simp only [synthValue] at h
      split at h
      next T' ht =>
        cases h
        exact .lam (synthTm_sound ht)
      next => cases h
  | .obj Tel ds => fun h => by
      simp only [synthValue] at h
      split at h
      next hds =>
        cases h
        exact .obj (checkDefs_sound hds)
      next => cases h
  | .cast v e => fun h => by
      simp only [synthValue] at h
      split at h
      next S S' T' hv he =>
        split at h
        next hS =>
          subst hS
          cases h
          exact .cast (synthValue_sound hv) (synthLe_sound he)
        next => cases h
      next => cases h
theorem checkDefs_sound {Γ : Ctx s} {p : Path s} {ds : Defs s} {Tel : Telescope (s,x)} : checkDefs Γ p ds Tel = true → Defs.HasType Γ p ds Tel :=
  match ds with
  | .nil => fun h => by
      simp only [checkDefs] at h
      split at h
      next => exact .nil
      next => cases h
  | .typ ds A U => fun h => by
      simp only [checkDefs] at h
      split at h
      next Tel W X X' W' =>
        rw [Bool.and_eq_true, decide_eq_true_iff] at h
        obtain ⟨⟨rfl, rfl, rfl, hA, hU⟩, hds⟩ := h
        exact .typ (checkDefs_sound hds) hA hU
      next => cases h
  | .fld ds a (.path P) => fun h => by
      simp only [checkDefs] at h
      split at h
      next Tel a' q' =>
        split at h
        next q T hq hP =>
          rw [Bool.and_eq_true, decide_eq_true_iff] at h
          obtain ⟨⟨rfl, ha, hpath⟩, hds⟩ := h
          rw [Path.unweaken_iff] at hq
          subst hq
          exact .path (checkDefs_sound hds) ha (synthPath_sound hP) hpath
        next => cases h
      next => cases h
  | .fld ds a (.fn v) => fun h => by
      simp only [checkDefs] at h
      split at h
      next Tel a' S T =>
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
        obtain ⟨⟨⟨rfl, ha, hl⟩, hv⟩, hds⟩ := h
        exact .fn (checkDefs_sound hds) ha hl (synthValue_sound hv)
      next => cases h
  | .fld ds a (.nest Tel'' ds') => fun h => by
      simp only [checkDefs] at h
      split at h
      next Tel a' Tel' =>
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h
        obtain ⟨⟨⟨rfl, ha, rfl⟩, hds'⟩, hds⟩ := h
        exact .nest (checkDefs_sound hds) ha (checkDefs_sound hds')
      next => cases h
end

end PDot.FCp
