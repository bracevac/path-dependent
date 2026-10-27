import Coercions.PDot.FCp.Canon
import Coercions.PDot.FCp.Checker

/-!
# Resolution and the normal type of FCp (plan X, T.6 amended)

One alias step `Ctx.next` reads the definition at the canonical name of a selection's prefix.
`Ctx.resFuel` iterates it with fuel, and the budget `Ctx.resBudget` is one more than the number of
type definitions in the context's blocks.  Resolution `Ctx.res` is `Ctx.resFuel` at the budget, and
it resolves a cycle of definitions to `⊤`.  `Ctx.res_stable` says that resolution commutes with one
alias step, and it is proved by stabilization over the type definitions.

The canonical types `TyO` read a type through a naming `CFn`, lifted under binders by `CFn.lift`.
The normal type `Ctx.norm` resolves the head and names every path by `Ctx.canon`.
`Ty.canonTy_subst` computes the canonical type of a substitution at every binder depth, by
`CFn.Hom.lift`.  Then come `canon_cons_opaque` and the laws of `norm`: `Ctx.norm_congr`,
`Ctx.norm_substPath`, `Ctx.norm_cod`, `Ctx.norm_pi` and `Ctx.norm_defAt`.

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- One alias step at the head of a type: the definition at the canonical name of its prefix. -/
def Ctx.next (Γ : Ctx s) : Ty s → Option (Ty s)
  | .sel p A => (Γ.canon p).bind (fun c => Γ.defAt c A)
  | _ => none  -- ⊥, Π(z : S) T with z bound in T, μ(w : Tel) with w bound in Tel

def Ctx.resFuel (Γ : Ctx s) : Nat → Ty s → Ty s
  | 0, T => match Γ.next T with | none => T | some _ => .top
  | n+1, T => match Γ.next T with | none => T | some W => Γ.resFuel n W

/-! ## The type definitions of a context and the budget -/

def TyDefs.all : TyDefs s → List (Ty s)
  | .nil => []
  | .cons W _ U => U :: W.all

mutual
def Block.defs : Block s → List (Ty s)
  | .node W C => W.all ++ C.defs
  | .fwd _ => []
  | .clo => []
def Kids.defs : Kids s → List (Ty s)
  | .nil => []
  | .cons C _ B => B.defs ++ C.defs
end

def Binding.defs : Binding s → List (Ty (s,x))
  | .opaque _ => []
  | .transparent _ B => B.defs

def Ctx.defs : Ctx s → List (Ty s)
  | .nil => []
  | .cons Γ b => Γ.defs.map (·.rename Rename.succ) ++ b.defs  -- z bound in b's block

/-- One more than the number of type definitions in the context's blocks. -/
def Ctx.resBudget (Γ : Ctx s) : Nat := Γ.defs.length + 1
def Ctx.res (Γ : Ctx s) (T : Ty s) : Ty s := Γ.resFuel Γ.resBudget T

theorem TyDefs.get_mem : ∀ (W : TyDefs s) (A : Label) (U : Ty s), W.get A = some U → U ∈ W.all
  | .nil, _, _, h => by cases h
  | .cons W A' U', A, U, h => by
      by_cases e : A = A'
      · have : TyDefs.get (.cons W A' U') A = some U' := by simp [TyDefs.get, e]
        rw [this] at h; cases h; exact List.mem_cons_self ..
      · have : TyDefs.get (.cons W A' U') A = W.get A := by simp [TyDefs.get, e]
        rw [this] at h
        exact List.mem_cons_of_mem _ (TyDefs.get_mem W A U h)

theorem TyDefs.all_rename : ∀ (W : TyDefs s₁) (ρ : Rename s₁ s₂), (W.rename ρ).all = W.all.map (·.rename ρ)
  | .nil, _ => rfl
  | .cons W A U, ρ => by
      show U.rename ρ :: (W.rename ρ).all = _
      rw [TyDefs.all_rename W ρ]; rfl

mutual
theorem Block.defs_rename : ∀ (B : Block s₁) (ρ : Rename s₁ s₂), (B.rename ρ).defs = B.defs.map (·.rename ρ)
  | .node W C, ρ => by
      show (W.rename ρ).all ++ (C.rename ρ).defs = (W.all ++ C.defs).map _
      rw [TyDefs.all_rename, Kids.defs_rename C ρ, List.map_append]
  | .fwd _, _ => rfl
  | .clo, _ => rfl
theorem Kids.defs_rename : ∀ (C : Kids s₁) (ρ : Rename s₁ s₂), (C.rename ρ).defs = C.defs.map (·.rename ρ)
  | .nil, _ => rfl
  | .cons C a B, ρ => by
      show (B.rename ρ).defs ++ (C.rename ρ).defs = (B.defs ++ C.defs).map _
      rw [Block.defs_rename B ρ, Kids.defs_rename C ρ, List.map_append]
end

theorem Kids.get_defs : ∀ (C : Kids s) (a : Label) (B : Block s), C.get a = some B → ∀ T ∈ B.defs, T ∈ C.defs
  | .nil, _, _, h => by cases h
  | .cons C a' B', a, B, h => by
      intro T hT
      show T ∈ B'.defs ++ C.defs
      by_cases e : a = a'
      · have : Kids.get (.cons C a' B') a = some B' := by simp [Kids.get, e]
        rw [this] at h; cases h
        exact List.mem_append_left _ hT
      · have : Kids.get (.cons C a' B') a = C.get a := by simp [Kids.get, e]
        rw [this] at h
        exact List.mem_append_right _ (Kids.get_defs C a B h T hT)

theorem Ctx.blockAt_defs : ∀ (Γ : Ctx s) (x : BVar s .var) (B : Block s), Γ.blockAt x = some B →
    ∀ T ∈ B.defs, T ∈ Γ.defs
  | .cons Γ (.opaque _), .here, _, h => by cases h
  | .cons Γ (.transparent _ B'), .here, B, h => by
      cases h
      intro T hT
      exact List.mem_append_right _ hT
  | .cons Γ b, .there y, B, h => by
      intro T hT
      have h' : (Γ.blockAt y).map (Block.rename · Rename.succ) = some B := by cases b <;> exact h
      cases hy : Γ.blockAt y with
      | none => rw [hy] at h'; cases h'
      | some B₀ =>
          rw [hy] at h'
          cases h'
          rw [Block.defs_rename] at hT
          obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.mp hT
          exact List.mem_append_left _ (List.mem_map.mpr ⟨T₀, Ctx.blockAt_defs Γ y B₀ hy T₀ hT₀, rfl⟩)

theorem Ctx.nodeAt_defs (Γ : Ctx s) : ∀ (p : Path s) (B : Block s), Γ.nodeAt p = some B → ∀ T ∈ B.defs, T ∈ Γ.defs
  | .var x, B, h => Ctx.blockAt_defs Γ x B h
  | .sel p a, B, h => by
      have h' : (Γ.nodeAt p).bind (·.child a) = some B := h
      cases hp : Γ.nodeAt p with
      | none => rw [hp] at h'; cases h'
      | some B₀ =>
          rw [hp] at h'
          intro T hT
          apply Ctx.nodeAt_defs Γ p B₀ hp T
          cases B₀ with
          | node W C => exact List.mem_append_right _ (Kids.get_defs C a B h' T hT)
          | fwd _ => cases h'
          | clo => cases h'

theorem Ctx.defAt_mem (Γ : Ctx s) {p : Path s} {A : Label} {W : Ty s} (h : Γ.defAt p A = some W) : W ∈ Γ.defs := by
  have h' : (Γ.nodeAt p).bind (·.def A) = some W := h
  cases hp : Γ.nodeAt p with
  | none => rw [hp] at h'; cases h'
  | some B =>
      rw [hp] at h'
      apply Ctx.nodeAt_defs Γ p B hp W
      cases B with
      | node W' C => exact List.mem_append_left _ (TyDefs.get_mem W' A W h')
      | fwd _ => cases h'
      | clo => cases h'

theorem Ctx.next_mem (Γ : Ctx s) {T W : Ty s} (h : Γ.next T = some W) : W ∈ Γ.defs := by
  cases T with
  | sel p A =>
      have h' : (Γ.canon p).bind (fun c => Γ.defAt c A) = some W := h
      cases hc : Γ.canon p with
      | none => rw [hc] at h'; cases h'
      | some c => rw [hc] at h'; exact Γ.defAt_mem h'
  | bot => cases h
  | pi _ _ => cases h
  | mu _ => cases h

/-! ## Resolution is stable at the budget -/

def Ctx.resolvedAt (Γ : Ctx s) : Nat → Ty s → Bool
  | 0, T => (Γ.next T).isNone
  | n+1, T => match Γ.next T with | none => true | some W => Γ.resolvedAt n W

theorem Ctx.resolvedAt_mono (Γ : Ctx s) : ∀ n T, Γ.resolvedAt n T = true → Γ.resolvedAt (n+1) T = true
  | 0, T, h => by
      simp only [Ctx.resolvedAt] at h ⊢
      cases hT : Γ.next T with
      | none => rfl
      | some W => rw [hT] at h; cases h
  | n+1, T, h => by
      simp only [Ctx.resolvedAt] at h ⊢
      cases hT : Γ.next T with
      | none => rfl
      | some W => rw [hT] at h; exact Γ.resolvedAt_mono n W h

theorem Ctx.resFuel_resolved (Γ : Ctx s) : ∀ n T, Γ.resolvedAt n T = true → Γ.resFuel n T = Γ.resFuel (n+1) T
  | 0, T, h => by
      simp only [Ctx.resolvedAt] at h
      cases hT : Γ.next T with
      | none => simp only [Ctx.resFuel, hT]
      | some W => rw [hT] at h; cases h
  | n+1, T, h => by
      simp only [Ctx.resolvedAt] at h
      cases hT : Γ.next T with
      | none => simp only [Ctx.resFuel, hT]
      | some W =>
          rw [hT] at h
          show (match Γ.next T with | none => T | some W => Γ.resFuel n W) =
            (match Γ.next T with | none => T | some W => Γ.resFuel (n+1) W)
          rw [hT]
          exact Γ.resFuel_resolved n W h

theorem Ctx.resFuel_unresolved (Γ : Ctx s) : ∀ n T, Γ.resolvedAt n T = false → Γ.resFuel n T = .top
  | 0, T, h => by
      simp only [Ctx.resolvedAt] at h
      cases hT : Γ.next T with
      | none => rw [hT] at h; cases h
      | some W => simp only [Ctx.resFuel, hT]
  | n+1, T, h => by
      simp only [Ctx.resolvedAt] at h
      cases hT : Γ.next T with
      | none => rw [hT] at h; cases h
      | some W =>
          rw [hT] at h
          show (match Γ.next T with | none => T | some W => Γ.resFuel n W) = _
          rw [hT]
          exact Γ.resFuel_unresolved n W h

theorem Ctx.resolvedAt_stable (Γ : Ctx s) :
    ∀ W ∈ Γ.defs, Γ.resolvedAt Γ.defs.length W = Γ.resolvedAt (Γ.defs.length + 1) W := by
  refine stabilize Γ.defs (fun n W => Γ.resolvedAt n W) (Γ.resolvedAt_mono) ?_
  intro n hn T _
  show Γ.resolvedAt (n+1) T = Γ.resolvedAt (n+2) T
  simp only [Ctx.resolvedAt]
  cases hT : Γ.next T with
  | none => rfl
  | some W => exact hn W (Γ.next_mem hT)

/-- `res_stable`: resolution commutes with one alias step. -/
theorem Ctx.res_stable (Γ : Ctx s) {T W : Ty s} (h : Γ.next T = some W) : Γ.res T = Γ.res W := by
  show Γ.resFuel (Γ.defs.length + 1) T = Γ.resFuel (Γ.defs.length + 1) W
  have e1 : Γ.resFuel (Γ.defs.length + 1) T = Γ.resFuel Γ.defs.length W := by
    show (match Γ.next T with | none => T | some W => Γ.resFuel Γ.defs.length W) = _
    rw [h]
  rw [e1]
  have hs := Γ.resolvedAt_stable W (Γ.next_mem h)
  cases hb : Γ.resolvedAt Γ.defs.length W with
  | true => exact Γ.resFuel_resolved _ W hb
  | false =>
      rw [hb] at hs
      rw [Γ.resFuel_unresolved _ W hb, Γ.resFuel_unresolved _ W hs.symm]

theorem Ctx.res_settled (Γ : Ctx s) {T : Ty s} (h : Γ.next T = none) : Γ.res T = T := by
  show Γ.resFuel (Γ.defs.length + 1) T = T
  simp only [Ctx.resFuel, h]

theorem Ctx.res_bot (Γ : Ctx s) : Γ.res .bot = .bot := Γ.res_settled rfl
theorem Ctx.res_pi (Γ : Ctx s) (S : Ty s) (T : Ty (s,x)) : Γ.res (.pi S T) = .pi S T := Γ.res_settled rfl
theorem Ctx.res_mu (Γ : Ctx s) (Tel : Telescope (s,x)) : Γ.res (.mu Tel) = .mu Tel := Γ.res_settled rfl

/-- `defAt_canon`: the alias step reads the definition at the canonical name. -/
theorem Ctx.defAt_canon (Γ : Ctx s) {p c : Path s} (h : Γ.canon p = some c) (A : Label) :
    Γ.next (.sel p A) = Γ.defAt c A := by
  show (Γ.canon p).bind (fun c => Γ.defAt c A) = _
  rw [h]; rfl

/-- At a node of the context, the alias step is the definition itself. -/
theorem Ctx.next_node (Γ : Ctx s) {p : Path s} {A : Label} {W : Ty s} (h : Γ.defAt p A = some W) :
    Γ.next (.sel p A) = some W := by
  have h' : (Γ.nodeAt p).bind (·.def A) = some W := h
  cases hp : Γ.nodeAt p with
  | none => rw [hp] at h'; cases h'
  | some B =>
      cases B with
      | node W' C =>
          rw [Γ.defAt_canon (canon_node Γ hp)]
          exact h
      | fwd _ => rw [hp] at h'; cases h'
      | clo => rw [hp] at h'; cases h'

theorem Ctx.res_defAt (Γ : Ctx s) {p : Path s} {A : Label} {W : Ty s} (h : Γ.defAt p A = some W) :
    Γ.res (.sel p A) = Γ.res W := Γ.res_stable (Γ.next_node h)

/-! ## Canonical types: paths named by `canon`, `none` at every cyclic path -/

mutual
inductive TyO : Sig → Type where
  | bot : TyO s
  | sel : Option (Path s) → Label → TyO s
  | pi : TyO s → TyO (s,x) → TyO s  -- Π(z : S) T, z the .here of T
  | mu : TelO (s,x) → TyO s  -- μ(w : Tel), w the .here of Tel
inductive PrO : Sig → Type where
  | le : TyO s → TyO s → PrO s
  | fld : Label → TyO s → PrO s
  | alias : Option (Path s) → PrO s
  | is : TyO s → PrO s
inductive TelO : Sig → Type where
  | nil : TelO s
  | cons : TelO s → PrO s → TelO s
end

deriving instance DecidableEq for TyO, PrO, TelO

/-- A naming of the paths of a signature. -/
abbrev CFn (s : Sig) := Path s → Option (Path s)

/-- Under a binder: a path rooted at the binder names itself, any other path is named as before. -/
def CFn.lift (c : CFn s) : CFn (s,x) := fun p =>
  match Path.unweaken p with
  | none => some p  -- p rooted at the new binder
  | some p' => (c p').map (·.rename Rename.succ)

mutual
def Ty.canonTy (c : CFn s) : Ty s → TyO s
  | .bot => .bot
  | .sel p A => .sel (c p) A
  | .pi S T => .pi (S.canonTy c) (T.canonTy c.lift)  -- z bound in T
  | .mu Tel => .mu (Tel.canonTel c.lift)  -- w bound in Tel
def Pr.canonPr (c : CFn s) : Pr s → PrO s
  | .le S T => .le (S.canonTy c) (T.canonTy c)
  | .fld a T => .fld a (T.canonTy c)
  | .alias q => .alias (c q)
  | .is T => .is (T.canonTy c)
def Telescope.canonTel (c : CFn s) : Telescope s → TelO s
  | .nil => .nil
  | .cons Tel pr => .cons (Tel.canonTel c) (pr.canonPr c)
end

/-- The normal type: resolve the head, then name every path by `canon`. -/
def Ctx.norm (Γ : Ctx s) (T : Ty s) : TyO s := (Γ.res T).canonTy Γ.canon

/-! ## Laws of `unweaken` -/

theorem Path.unweaken_rename_succ (p : Path s) : Path.unweaken (p.rename (Rename.succ (k := .var))) = some p :=
  Path.unweaken_iff.2 rfl

theorem Path.eq_of_unweaken {p : Path (s,x)} {p' : Path s} (h : Path.unweaken p = some p') :
    p = p'.rename Rename.succ :=
  Path.unweaken_iff.1 h

theorem Path.root_rename_succ (p : Path s) : (p.rename (Rename.succ (k := .var))).root = .there p.root := by
  induction p with
  | var y => rfl
  | sel p a ih => exact ih

theorem Path.unweaken_none_of_root {p : Path (s,x)} (h : p.root = .here) : Path.unweaken p = none := by
  cases hp : Path.unweaken p with
  | none => rfl
  | some q =>
      rw [Path.eq_of_unweaken hp, Path.root_rename_succ] at h
      cases h

theorem Path.root_of_unweaken_none {p : Path (s,x)} (h : Path.unweaken p = none) : p.root = .here := by
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · exact hr
  · rw [show Path.unweaken p₀.weaken = some p₀ from Path.unweaken_iff.2 rfl] at h; cases h

theorem Path.root_subst_lift {σ : PathSubst s₁ s₂} : ∀ {p : Path (s₁,x)}, p.root = .here → (p.subst σ.lift).root = .here
  | .var .here, _ => rfl
  | .var (.there _), h => by cases h
  | .sel p _, h => Path.root_subst_lift (p := p) h

theorem Path.unweaken_subst_lift_none {σ : PathSubst s₁ s₂} {p : Path (s₁,x)} (h : Path.unweaken p = none) :
    Path.unweaken (p.subst σ.lift) = none :=
  Path.unweaken_none_of_root (Path.root_subst_lift (Path.root_of_unweaken_none h))

theorem Path.weaken_subst_lift' (p : Path s₁) (σ : PathSubst s₁ s₂) :
    (p.rename (Rename.succ (k := .var))).subst σ.lift = (p.subst σ).rename Rename.succ := by
  induction p with
  | var y => rfl
  | sel p a ih => exact congrArg (Path.sel · a) ih

theorem CFn.lift_rename_succ (c : CFn s) (p : Path s) :
    c.lift (p.rename Rename.succ) = (c p).map (·.rename Rename.succ) := by
  simp only [CFn.lift, Path.unweaken_rename_succ]

theorem CFn.lift_of_none (c : CFn s) {p : Path (s,x)} (h : Path.unweaken p = none) : c.lift p = some p := by
  simp only [CFn.lift, h]

/-! ## The canonical type of a substitution

`CFn.Hom c₁ c₂ σ` says that naming after `σ` is naming before `σ`, then after it.  It lifts under
binders, so the canonical type of `T.subst σ` is computed from the canonical type of `T`. -/

def CFn.Hom (c₁ : CFn s₁) (c₂ : CFn s₂) (σ : PathSubst s₁ s₂) : Prop :=
  ∀ r, c₂ (r.subst σ) = (c₁ r).bind (fun d => c₂ (d.subst σ))

theorem CFn.Hom.lift {c₁ : CFn s₁} {c₂ : CFn s₂} {σ : PathSubst s₁ s₂} (h : CFn.Hom c₁ c₂ σ) :
    CFn.Hom c₁.lift c₂.lift σ.lift := by
  intro r
  cases hr : Path.unweaken r with
  | none =>
      have h2 := Path.unweaken_subst_lift_none (σ := σ) hr
      rw [CFn.lift_of_none c₁ hr, CFn.lift_of_none c₂ h2]
      simp only [Option.bind_some]
      rw [CFn.lift_of_none c₂ h2]
  | some r' =>
      have er := Path.eq_of_unweaken hr
      subst er
      rw [Path.weaken_subst_lift', CFn.lift_rename_succ, CFn.lift_rename_succ, h r']
      cases c₁ r' with
      | none => rfl
      | some d =>
          simp only [Option.map_some, Option.bind_some]
          rw [Path.weaken_subst_lift', CFn.lift_rename_succ]

mutual
def TyO.bindS (c : CFn s₂) (σ : PathSubst s₁ s₂) : TyO s₁ → TyO s₂
  | .bot => .bot
  | .sel o A => .sel (o.bind (fun d => c (d.subst σ))) A
  | .pi S T => .pi (S.bindS c σ) (T.bindS c.lift σ.lift)  -- z bound in T
  | .mu Tel => .mu (Tel.bindS c.lift σ.lift)  -- w bound in Tel
def PrO.bindS (c : CFn s₂) (σ : PathSubst s₁ s₂) : PrO s₁ → PrO s₂
  | .le S T => .le (S.bindS c σ) (T.bindS c σ)
  | .fld a T => .fld a (T.bindS c σ)
  | .alias o => .alias (o.bind (fun d => c (d.subst σ)))
  | .is T => .is (T.bindS c σ)
def TelO.bindS (c : CFn s₂) (σ : PathSubst s₁ s₂) : TelO s₁ → TelO s₂
  | .nil => .nil
  | .cons Tel pr => .cons (Tel.bindS c σ) (pr.bindS c σ)
end

mutual
theorem Ty.canonTy_subst : ∀ (T : Ty s₁) {c₁ : CFn s₁} {c₂ : CFn s₂} {σ : PathSubst s₁ s₂},
    CFn.Hom c₁ c₂ σ → (T.subst σ).canonTy c₂ = (T.canonTy c₁).bindS c₂ σ
  | .bot, _, _, _, _ => rfl
  | .sel p A, _, _, _, h => by
      simp only [Ty.subst, Ty.canonTy, TyO.bindS]
      rw [h p]
  | .pi S T, _, _, _, h => by
      show TyO.pi _ _ = TyO.pi _ _
      rw [Ty.canonTy_subst S h, Ty.canonTy_subst T h.lift]
  | .mu Tel, _, _, _, h => by
      show TyO.mu _ = TyO.mu _
      rw [Telescope.canonTel_subst Tel h.lift]
theorem Pr.canonPr_subst : ∀ (pr : Pr s₁) {c₁ : CFn s₁} {c₂ : CFn s₂} {σ : PathSubst s₁ s₂},
    CFn.Hom c₁ c₂ σ → (pr.subst σ).canonPr c₂ = (pr.canonPr c₁).bindS c₂ σ
  | .le S T, _, _, _, h => by
      show PrO.le _ _ = PrO.le _ _
      rw [Ty.canonTy_subst S h, Ty.canonTy_subst T h]
  | .fld a T, _, _, _, h => by
      show PrO.fld a _ = PrO.fld a _
      rw [Ty.canonTy_subst T h]
  | .alias q, _, _, _, h => by
      simp only [Pr.subst, Pr.canonPr, PrO.bindS]
      rw [h q]
  | .is T, _, _, _, h => by
      show PrO.is _ = PrO.is _
      rw [Ty.canonTy_subst T h]
theorem Telescope.canonTel_subst : ∀ (Tel : Telescope s₁) {c₁ : CFn s₁} {c₂ : CFn s₂} {σ : PathSubst s₁ s₂},
    CFn.Hom c₁ c₂ σ → (Tel.subst σ).canonTel c₂ = (Tel.canonTel c₁).bindS c₂ σ
  | .nil, _, _, _, _ => rfl
  | .cons Tel pr, _, _, _, h => by
      show TelO.cons _ _ = TelO.cons _ _
      rw [Telescope.canonTel_subst Tel h, Pr.canonPr_subst pr h]
end

/-! ## Congruence of naming under substitution -/

/-- A naming that respects selection. -/
def CFn.Cong (c : CFn s) : Prop := ∀ p q a, c p = c q → c (.sel p a) = c (.sel q a)

theorem CFn.Cong.subst {c : CFn s₂} (hc : CFn.Cong c) {σ σ' : PathSubst s₁ s₂}
    (h : ∀ y, c (σ.var y) = c (σ'.var y)) : ∀ d : Path s₁, c (d.subst σ) = c (d.subst σ')
  | .var y => h y
  | .sel d a => hc _ _ a (CFn.Cong.subst hc h d)

theorem Path.rename_succ_inj {p q : Path s} (h : p.rename (Rename.succ (k := .var)) = q.rename Rename.succ) : p = q := by
  have := congrArg Path.unweaken h
  rw [Path.unweaken_rename_succ, Path.unweaken_rename_succ] at this
  cases this; rfl

theorem Option.map_rename_succ_inj {o o' : Option (Path s)}
    (h : o.map (·.rename (Rename.succ (k := .var))) = o'.map (·.rename Rename.succ)) : o = o' := by
  cases o <;> cases o' <;> simp at h
  · rfl
  · rw [Path.rename_succ_inj h]

theorem CFn.Cong.lift {c : CFn s} (hc : CFn.Cong c) : CFn.Cong c.lift := by
  intro p q a h
  cases hp : Path.unweaken p with
  | none =>
      cases hq : Path.unweaken q with
      | none =>
          have h' : some p = some q := by
            have := h
            simp only [CFn.lift, hp, hq] at this
            exact this
          cases h'; rfl
      | some q' =>
          exfalso
          have h' : some p = (c q').map (·.rename (Rename.succ (k := .var))) := by
            have := h
            simp only [CFn.lift, hp, hq] at this
            exact this
          cases hcq : c q' with
          | none => rw [hcq] at h'; cases h'
          | some d =>
              rw [hcq] at h'
              cases h'
              rw [Path.unweaken_rename_succ] at hp
              cases hp
  | some p' =>
      cases hq : Path.unweaken q with
      | none =>
          exfalso
          have h' : (c p').map (·.rename (Rename.succ (k := .var))) = some q := by
            have := h
            simp only [CFn.lift, hp, hq] at this
            exact this
          cases hcp : c p' with
          | none => rw [hcp] at h'; cases h'
          | some d =>
              rw [hcp] at h'
              cases h'
              rw [Path.unweaken_rename_succ] at hq
              cases hq
      | some q' =>
          have h' : (c p').map (·.rename (Rename.succ (k := .var))) = (c q').map (·.rename (Rename.succ (k := .var))) := by
            have := h
            simp only [CFn.lift, hp, hq] at this
            exact this
          have e := hc p' q' a (Option.map_rename_succ_inj h')
          rw [Path.eq_of_unweaken hp, Path.eq_of_unweaken hq]
          show c.lift ((p'.sel a).rename Rename.succ) = c.lift ((q'.sel a).rename Rename.succ)
          rw [CFn.lift_rename_succ, CFn.lift_rename_succ, e]

theorem CFn.Cong.lift_pointwise {c : CFn s₂} {σ σ' : PathSubst s₁ s₂}
    (h : ∀ y, c (σ.var y) = c (σ'.var y)) : ∀ y, c.lift (σ.lift.var y) = c.lift (σ'.lift.var y)
  | .here => rfl
  | .there y => by
      show c.lift ((σ.var y).rename Rename.succ) = c.lift ((σ'.var y).rename Rename.succ)
      rw [CFn.lift_rename_succ, CFn.lift_rename_succ, h y]

mutual
theorem TyO.bindS_congr : ∀ (X : TyO s₁) {c : CFn s₂} {σ σ' : PathSubst s₁ s₂}, CFn.Cong c →
    (∀ y, c (σ.var y) = c (σ'.var y)) → X.bindS c σ = X.bindS c σ'
  | .bot, _, _, _, _, _ => rfl
  | .sel o A, _, _, _, hc, h => by
      show TyO.sel _ A = TyO.sel _ A
      cases o with
      | none => rfl
      | some d =>
          simp only [Option.bind_some]
          rw [CFn.Cong.subst hc h d]
  | .pi S T, _, _, _, hc, h => by
      show TyO.pi _ _ = TyO.pi _ _
      rw [TyO.bindS_congr S hc h, TyO.bindS_congr T hc.lift (CFn.Cong.lift_pointwise h)]
  | .mu Tel, _, _, _, hc, h => by
      show TyO.mu _ = TyO.mu _
      rw [TelO.bindS_congr Tel hc.lift (CFn.Cong.lift_pointwise h)]
theorem PrO.bindS_congr : ∀ (X : PrO s₁) {c : CFn s₂} {σ σ' : PathSubst s₁ s₂}, CFn.Cong c →
    (∀ y, c (σ.var y) = c (σ'.var y)) → X.bindS c σ = X.bindS c σ'
  | .le S T, _, _, _, hc, h => by
      show PrO.le _ _ = PrO.le _ _
      rw [TyO.bindS_congr S hc h, TyO.bindS_congr T hc h]
  | .fld a T, _, _, _, hc, h => by
      show PrO.fld a _ = PrO.fld a _
      rw [TyO.bindS_congr T hc h]
  | .alias o, _, _, _, hc, h => by
      show PrO.alias _ = PrO.alias _
      cases o with
      | none => rfl
      | some d =>
          simp only [Option.bind_some]
          rw [CFn.Cong.subst hc h d]
  | .is T, _, _, _, hc, h => by
      show PrO.is _ = PrO.is _
      rw [TyO.bindS_congr T hc h]
theorem TelO.bindS_congr : ∀ (X : TelO s₁) {c : CFn s₂} {σ σ' : PathSubst s₁ s₂}, CFn.Cong c →
    (∀ y, c (σ.var y) = c (σ'.var y)) → X.bindS c σ = X.bindS c σ'
  | .nil, _, _, _, _, _ => rfl
  | .cons Tel pr, _, _, _, hc, h => by
      show TelO.cons _ _ = TelO.cons _ _
      rw [TelO.bindS_congr Tel hc h, PrO.bindS_congr pr hc h]
end

/-! ## The laws of `norm` -/

theorem Ctx.canon_cong (Γ : Ctx s) : CFn.Cong Γ.canon := fun _ _ a h => canon_sel_congr Γ h a

/-- `canon_substPath` at the hole of a type: naming after instantiating the hole by `p` is naming
under the hole, then after it. -/
theorem Ctx.canon_hom_one (Γ : Ctx s) (p : Path s) : CFn.Hom (CFn.lift Γ.canon) Γ.canon (PathSubst.one p) := by
  intro r
  cases hr : Path.unweaken r with
  | none =>
      show _ = (match Path.unweaken r with | none => some r | some p' => _).bind _
      rw [hr]; rfl
  | some r' =>
      rw [Path.eq_of_unweaken hr]
      rw [CFn.lift_rename_succ]
      rw [show (r'.rename Rename.succ).subst (PathSubst.one p) = r' from by
        rw [Path.subst_one]; exact Path.weaken_substPath r' p]
      cases hc : Γ.canon r' with
      | none => rfl
      | some d =>
          simp only [Option.map_some, Option.bind_some]
          rw [show (d.rename Rename.succ).subst (PathSubst.one p) = d from by
            rw [Path.subst_one]; exact Path.weaken_substPath d p]
          exact (canon_idem Γ hc).symm

theorem Ty.canonTy_substPath (Γ : Ctx s) (T : Ty (s,x)) (p : Path s) :
    (T.substPath p).canonTy Γ.canon = (T.canonTy (CFn.lift Γ.canon)).bindS Γ.canon (PathSubst.one p) :=
  Ty.canonTy_subst T (Γ.canon_hom_one p)

theorem Ty.canonTy_substPath_congr (Γ : Ctx s) (T : Ty (s,x)) {p q : Path s} (h : Γ.canon p = Γ.canon q) :
    (T.substPath p).canonTy Γ.canon = (T.substPath q).canonTy Γ.canon := by
  rw [Ty.canonTy_substPath, Ty.canonTy_substPath]
  apply TyO.bindS_congr _ Γ.canon_cong
  intro y
  cases y with
  | here => exact h
  | there y => rfl

/-- `norm_congr`: two types with one canonical type have one normal type. -/
theorem Ctx.norm_congr (Γ : Ctx s) {S S' : Ty s} (h : S.canonTy Γ.canon = S'.canonTy Γ.canon) :
    Γ.norm S = Γ.norm S' := by
  cases S with
  | bot =>
      cases S' with
      | bot => rfl
      | sel _ _ => cases h
      | pi _ _ => cases h
      | mu _ => cases h
  | pi S₁ T₁ =>
      cases S' with
      | pi S₂ T₂ =>
          unfold Ctx.norm
          rw [Γ.res_pi, Γ.res_pi]
          exact h
      | bot => cases h
      | sel _ _ => cases h
      | mu _ => cases h
  | mu Tel =>
      cases S' with
      | mu Tel' =>
          unfold Ctx.norm
          rw [Γ.res_mu, Γ.res_mu]
          exact h
      | bot => cases h
      | sel _ _ => cases h
      | pi _ _ => cases h
  | sel p A =>
      cases S' with
      | sel p' A' =>
          have h' : TyO.sel (Γ.canon p) A = TyO.sel (Γ.canon p') A' := h
          injection h' with _ hcp hA
          subst hA
          have hn : Γ.next (.sel p A) = Γ.next (.sel p' A) := by
            show (Γ.canon p).bind _ = (Γ.canon p').bind _
            rw [hcp]
          cases hnx : Γ.next (.sel p A) with
          | none =>
              unfold Ctx.norm
              rw [Γ.res_settled hnx, Γ.res_settled (hn ▸ hnx)]
              exact h
          | some W =>
              unfold Ctx.norm
              rw [Γ.res_stable hnx, Γ.res_stable (show Γ.next (.sel p' A) = some W from hn ▸ hnx)]
      | bot => cases h
      | pi _ _ => cases h
      | mu _ => cases h

/-- `norm_substPath`: aliased paths give one normal type to every instance of a hole. -/
theorem Ctx.norm_substPath (Γ : Ctx s) (T : Ty (s,x)) {p q : Path s} (h : Γ.canon p = Γ.canon q) :
    Γ.norm (T.substPath p) = Γ.norm (T.substPath q) :=
  Γ.norm_congr (Ty.canonTy_substPath_congr Γ T h)

/-- The codomain law: one canonical codomain under the binder gives one normal type at every
argument. -/
theorem Ctx.norm_cod (Γ : Ctx s) {T₁ T₂ : Ty (s,x)} (h : T₁.canonTy (CFn.lift Γ.canon) = T₂.canonTy (CFn.lift Γ.canon))
    (p : Path s) : Γ.norm (T₁.substPath p) = Γ.norm (T₂.substPath p) := by
  apply Γ.norm_congr
  rw [Ty.canonTy_substPath, Ty.canonTy_substPath, h]

theorem Ctx.norm_pi (Γ : Ctx s) (S : Ty s) (T : Ty (s,x)) :
    Γ.norm (.pi S T) = .pi (S.canonTy Γ.canon) (T.canonTy (CFn.lift Γ.canon)) := by
  unfold Ctx.norm; rw [Γ.res_pi]; rfl

theorem Ctx.norm_defAt (Γ : Ctx s) {p : Path s} {A : Label} {W : Ty s} (h : Γ.defAt p A = some W) :
    Γ.norm (.sel p A) = Γ.norm W := by
  unfold Ctx.norm; rw [Γ.res_defAt h]

/-! ## Resolution settles, and aliased prefixes resolve alike -/

theorem Ctx.next_resFuel (Γ : Ctx s) : ∀ n T, Γ.next (Γ.resFuel n T) = none
  | 0, T => by
      cases hT : Γ.next T with
      | none => simp only [Ctx.resFuel, hT]
      | some _ => simp only [Ctx.resFuel, hT]; rfl
  | n+1, T => by
      cases hT : Γ.next T with
      | none => simp only [Ctx.resFuel, hT]
      | some W => simp only [Ctx.resFuel, hT]; exact Γ.next_resFuel n W

theorem Ctx.next_res (Γ : Ctx s) (T : Ty s) : Γ.next (Γ.res T) = none := Γ.next_resFuel _ T
theorem Ctx.res_res (Γ : Ctx s) (T : Ty s) : Γ.res (Γ.res T) = Γ.res T := Γ.res_settled (Γ.next_res T)

theorem Ctx.next_sel_congr (Γ : Ctx s) {P₁ P₂ : Path s} (h : Γ.canon P₁ = Γ.canon P₂) (A : Label) :
    Γ.next (.sel P₁ A) = Γ.next (.sel P₂ A) := by
  show (Γ.canon P₁).bind _ = (Γ.canon P₂).bind _
  rw [h]

/-- Two selections at aliased prefixes resolve alike, or both are abstract. -/
theorem Ctx.res_sel_cases (Γ : Ctx s) {P₁ P₂ : Path s} (h : Γ.canon P₁ = Γ.canon P₂) (A : Label) :
    (Γ.next (.sel P₁ A) = none ∧ Γ.next (.sel P₂ A) = none ∧ Γ.res (.sel P₁ A) = .sel P₁ A ∧
      Γ.res (.sel P₂ A) = .sel P₂ A) ∨ Γ.res (.sel P₁ A) = Γ.res (.sel P₂ A) := by
  have hn := Γ.next_sel_congr h A
  cases h₁ : Γ.next (.sel P₁ A) with
  | none =>
      rw [h₁] at hn
      exact .inl ⟨rfl, hn.symm, Γ.res_settled h₁, Γ.res_settled hn.symm⟩
  | some W =>
      rw [h₁] at hn
      exact .inr ((Γ.res_stable h₁).trans (Γ.res_stable hn.symm).symm)

/-- Under an opaque binder the context's naming is the lifted naming, so `Ty.canonTy Γ.canon` reads
types under binders as the plan's `(Γ, z : opaque ⊤).canonTy` does. -/
theorem canon_cons_opaque (Γ : Ctx s) (T : Ty s) : (Γ.cons (.opaque T)).canon = CFn.lift Γ.canon := by
  funext p
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · rw [canon_here Γ T p hr, CFn.lift_of_none _ (Path.unweaken_none_of_root hr)]
  · rw [show p₀.weaken (k := .var) = p₀.rename Rename.succ from rfl, canon_weaken, CFn.lift_rename_succ]

end PDot.FCp
