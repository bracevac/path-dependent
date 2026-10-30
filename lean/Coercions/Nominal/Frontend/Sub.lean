import Coercions.Nominal.Frontend.Look

/-!
# Subtyping search with two goal kinds and replacement

`sub? Γ S T` searches a derivation of `Sub Γ S T`, and `path? Γ p T` one of
`HasTy Γ (.path p) T`.  This is plan XI (`plan-11-pdot-frontends.md`), its
parts "Shape", "A path at a type, in order", "Subtyping, in order" with
replacement, and "What the typer leaves out".  The model is
`lean/Coercions/Paths/Frontend/Sub.lean`.  pDOT has one `HasTy` for variables
and paths, so the goals are of two kinds, `Q.sub` and `Q.path`.

A path goal `path Γ p T` tries, in this order:

- G1.  A view of `p` equal to `T`, with the view's derivation (`viewAt`).
- G2.  `T = T₁ ∧ T₂`: both goals `path Γ p T₁` and `path Γ p T₂`, by
  `ty_and_intro`.  Final: nothing after G2 is tried.
- G3.  `T = μ(z. W)`: the goal `path Γ p W⟨p⟩`, by `ty_rec_intro`.
- G4.  A view `U` of `p` with `sub Γ U T`, by `ty_sub`.
- G5.  `T = {a : U}`: the goal `path Γ (p.a) U`, by `ty_rcd_intro`.
- G6.  `T = q.A`: the goal `path Γ p L` for each member `{A : L..U}` of a
  view of `q` with `L ≠ ⊥`, by `ty_sub` and `subtyp_sel2`.

A subtyping goal `sub Γ S T` tries, in this order:

- S1.  `S = T`, by `subtyp_refl`.
- S2.  `T = ⊤`, by `subtyp_top`.
- S3.  `S = ⊥`, by `subtyp_bot`.
- S4.  `T = T₁ ∧ T₂`: both goals `sub Γ S T₁` and `sub Γ S T₂`, by
  `subtyp_and2`.  Final: nothing after S4 is tried.
- S5.  Two records at one label, by `subtyp_fld` or `subtyp_typ`, or two
  function types, by `subtyp_all` with the codomains under `z : S₂`.
- S6a.  Replacement on the left.  `S` is a selection or a singleton at
  `l₀.nomExt bs`, and `l₀` has a view `m.type`.  Then `subtyp_sngl_pq` takes `S`
  to the same type at `m.nomExt bs`, and the goal goes on from there by
  `subtyp_trans`.
- S6b.  Replacement on the right, the mirror of S6a, by `subtyp_sngl_qp`.
- S6c.  Two `μ` types whose bodies differ at a pair of paths.  The first
  difference is read back to the outer signature.  One occurrence is replaced
  by `subtyp_sngl_pq` or `subtyp_sngl_qp`, with the witness `l₀ : r₀.type` or
  `r₀ : l₀.type`, then the goal goes on by `subtyp_trans`.
- S7.  `T = q.A`: the goal `sub Γ S L` for each member `{A : L..U}` of a view
  of `q` with `L ≠ ⊥`, by `subtyp_trans` and `subtyp_sel2`.
- S8.  `S = q.A`: the goal `sub Γ U T` for each member `{A : L..U}` of a view
  of `q`, by `subtyp_trans` and `subtyp_sel1`.
- S9.  `S = S₁ ∧ S₂`: the goal `sub Γ S₁ T`, else `sub Γ S₂ T`, by
  `subtyp_trans` with `subtyp_and11` or `subtyp_and12`.

Every replacement step gets its `Repl` derivation from `Repl.find?`, so a step
with a wrong replacement cannot be built.  The search chooses the split and
the witness, and `Repl.find?` checks the replaced type.  An occurrence rooted
at a binder inside a `μ` body is not read back and is not replaced, since
`rbnd` and `rall2` replace weakened outer paths only.

The run is the one of `Frontend/Fuel.lean`.  A goal is pending while its
alternatives run.  A pending goal met again on the same branch has no answer.
This is the cut, and it leaves the tank unmarked.  Each goal drawn costs
`cost` of the number of goals pending.  Out of fuel, the tank is marked.

The order causes some of the ways out of plan XI's list.  L1: `subtyp_trans`
through a middle type that is none of a bound read off a view, an operand of
`∧`, a replacement step or a view.  L2: `ty_rcd_intro`, `ty_rec_intro` or
`ty_and_intro` used to build a view rather than to meet a goal of that shape.
L5: replacement at a place S6 does not walk, which includes a `μ` pair whose
first difference is rooted at an inner binder.  L7: a member of `⊥`, since a
view `⊥` gives no member.  L8: a derivation past the fuel, or one that repeats
a goal along a branch.  The finality of G2 and S4 is part of L1 and L2.  L3,
L4 and L6 concern terms and definitions, which this module does not type.

Every answer carries its derivation, so there is no soundness theorem.  The
frame lemmas say that a run whose answer leaves the tank unmarked gives the
same answer with more fuel (`sub?_mono`, `path?_mono`).  Every definition is
structural, and the tests at the end run by `decide +kernel`.
-/

namespace NominalFrontend.Core

open Frontend.Fuel
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Ctx HasTy Sub Repl)
open Nominal.FCn (PRename)

/-! ## Goals and answers -/

/-- A goal without its context. -/
inductive Q (s : Sig) where
  | sub (S T : Ty s)                  -- answered by Sub Γ S T
  | path (p : Path s) (T : Ty s)      -- answered by HasTy Γ (.path p) T
deriving DecidableEq

/-- A goal in its context.  Two goals are equal only if their contexts are. -/
structure G where
  s : Sig
  Γ : Ctx s
  q : Q s
deriving DecidableEq

/-- The answer of a goal in the context `Γ`. -/
def RQ {s : Sig} (Γ : Ctx s) : Q s → Type
  | .sub S T => Sub Γ S T
  | .path p T => HasTy Γ (.path p) T
/-- The answer of a goal. -/
def R (g : G) : Type := RQ g.Γ g.q
/-- The oracle for the goals in one context. -/
abbrev Rec {s : Sig} (Γ : Ctx s) := (q : Q s) → Fu (Option (RQ Γ q))
/-- The codomains of two function types, under z : S₂. -/
abbrev RecAll {s : Sig} (Γ : Ctx s) :=
  (S₂ : Ty s) → (T₁ T₂ : Ty (s,x)) → Fu (Option (Sub (Γ.cons S₂) T₁ T₂))

/-! ## Syntax helpers -/

/-- Whether the type is an intersection. -/
def isAnd : Ty s → Bool
  | .and _ _ => true
  | _ => false
/-- The splits `l = l₀.nomExt bs`, from the whole path to the root. -/
def splits : Path s → List (Path s × List Label)
  | .var y => [(.var y, [])]
  | .sel l a => (.sel l a, []) :: (splits l).map fun e => (e.1, e.2 ++ [a])
/-- The prefixes `l₀`, `r₀` of `l = l₀.nomExt bs` and `r = r₀.nomExt bs`, whole paths first. -/
def commonSplits : Path s → Path s → List (Path s × Path s)
  | .sel l a, .sel r b => if a = b then (.sel l a, .sel r b) :: commonSplits l r else [(.sel l a, .sel r b)]
  | l, r => [(l, r)]
/-- The path of a selection or a singleton. -/
def leaf? : Ty s → Option (Path s)
  | .sel l _ => some l
  | .sngl l => some l
  | _ => none
/-- The same selection or singleton at another path. -/
def reroot : Ty s → Path s → Ty s
  | .sel _ A, m => .sel m A
  | .sngl _, m => .sngl m
  | T, _ => T
/-- Under one more binder, the new binder has no image. -/
def dropTop (f : PRename s₁ s₂) : PRename (s₁,x) s₂ := fun
  | .here => none
  | .there y => f y

/-! ## The first difference of two types

The walk goes left to right, skips equal parts, and stops at the first pair of
different paths in one position.  The paths are read back through `f`.  The
third component is the left type with that one path replaced by the right
one.  A different constructor, label or binder shape answers `none`. -/

mutual
/-- The first pair of different paths of two types, read back through `f`, with the left type replaced there. -/
def Ty.firstDiff? : Ty s₁ → Ty s₁ → PRename s₁ s₂ → Option (Path s₂ × Path s₂ × Ty s₁)
  | .rcd D, .rcd D', f => (Dec.firstDiff? D D' f).map fun e => (e.1, e.2.1, .rcd e.2.2)
  | .and T U, .and T' U', f =>
      if T = T' then (Ty.firstDiff? U U' f).map fun e => (e.1, e.2.1, .and T e.2.2)
      else (Ty.firstDiff? T T' f).map fun e => (e.1, e.2.1, .and e.2.2 U)
  | .sel l A, .sel r A', f =>
      if A = A' ∧ l ≠ r then
        match Nominal.FCn.Path.unrename l f, Nominal.FCn.Path.unrename r f with
        | some l', some r' => some (l', r', .sel r A)
        | _, _ => none
      else none
  | .mu T, .mu T', f => (Ty.firstDiff? T T' (dropTop f)).map fun e => (e.1, e.2.1, .mu e.2.2)   -- under z
  | .all S U, .all S' U', f =>
      if S = S' then (Ty.firstDiff? U U' (dropTop f)).map fun e => (e.1, e.2.1, .all S e.2.2)    -- under z
      else (Ty.firstDiff? S S' f).map fun e => (e.1, e.2.1, .all e.2.2 U)
  | .sngl l, .sngl r, f =>
      if l ≠ r then
        match Nominal.FCn.Path.unrename l f, Nominal.FCn.Path.unrename r f with
        | some l', some r' => some (l', r', .sngl r)
        | _, _ => none
      else none
  | _, _, _ => none
/-- The first pair of different paths of two declarations, as `Ty.firstDiff?`. -/
def Dec.firstDiff? : Dec s₁ → Dec s₁ → PRename s₁ s₂ → Option (Path s₂ × Path s₂ × Dec s₁)
  | .typ A S U, .typ A' S' U', f =>
      if A = A' then
        if S = S' then (Ty.firstDiff? U U' f).map fun e => (e.1, e.2.1, .typ A S e.2.2)
        else (Ty.firstDiff? S S' f).map fun e => (e.1, e.2.1, .typ A e.2.2 U)
      else none
  | .trm a T, .trm a' T', f =>
      if a = a' then (Ty.firstDiff? T T' f).map fun e => (e.1, e.2.1, .trm a e.2.2) else none
  | _, _, _ => none
end

/-! ## The alternatives of `sub` and `path` -/

section SubAlts
variable {s : Sig} {Γ : Ctx s}

/-- S1, `subtyp_refl`. -/
def sRefl (S T : Ty s) : Option (Sub Γ S T) := if h : S = T then some (h ▸ .subtyp_refl) else none     -- S1
/-- S2, `subtyp_top`. -/
def sTop (S T : Ty s) : Option (Sub Γ S T) := if h : T = .top then some (h ▸ .subtyp_top) else none   -- S2
/-- S3, `subtyp_bot`. -/
def sBot (S T : Ty s) : Option (Sub Γ S T) := if h : S = .bot then some (h ▸ .subtyp_bot) else none   -- S3

/-- S4, `subtyp_and2`. -/
def sAndR (r : Rec Γ) (S : Ty s) : (T : Ty s) → Fu (Option (Sub Γ S T))                              -- S4
  | .and T₁ T₂ => bindO (r (.sub S T₁)) fun e₁ => mapO (r (.sub S T₂)) fun e₂ => .subtyp_and2 e₁ e₂
  | _ => Fu.ret none

/-- `subtyp_fld` at two labels known equal. -/
def subFld {a b : Label} {S T : Ty s} (h : a = b) (e : Sub Γ S T) :
    Sub Γ (.rcd (.trm a S)) (.rcd (.trm b T)) := by
  cases h
  exact .subtyp_fld e
/-- `subtyp_typ` at two labels known equal. -/
def subTyp {A B : Label} {S₁ S₂ T₁ T₂ : Ty s} (h : A = B) (e₁ : Sub Γ S₂ S₁) (e₂ : Sub Γ T₁ T₂) :
    Sub Γ (.rcd (.typ A S₁ T₁)) (.rcd (.typ B S₂ T₂)) := by
  cases h
  exact .subtyp_typ e₁ e₂

/-- S5, `subtyp_fld`, `subtyp_typ`, `subtyp_all`. -/
def sStruct (r : Rec Γ) (rAll : RecAll Γ) : (S T : Ty s) → Fu (Option (Sub Γ S T))                  -- S5
  | .rcd (.trm a U₁), .rcd (.trm b U₂) =>
      if h : a = b then mapO (r (.sub U₁ U₂)) (subFld h) else Fu.ret none                              -- subtyp_fld
  | .rcd (.typ A L₁ U₁), .rcd (.typ B L₂ U₂) =>
      if h : A = B then bindO (r (.sub L₂ L₁)) fun e₁ => mapO (r (.sub U₁ U₂)) fun e₂ => subTyp h e₁ e₂ -- subtyp_typ
      else Fu.ret none
  | .all S₁ T₁, .all S₂ T₂ =>
      bindO (r (.sub S₂ S₁)) fun e₁ => mapO (rAll S₂ T₁ T₂) fun e₂ => .subtyp_all e₁ e₂               -- subtyp_all, T's under z : S₂
  | _, _ => Fu.ret none

/-- S6a, replacement on the left, `subtyp_sngl_pq` then `subtyp_trans`. -/
def sReplL (r : Rec Γ) (S T : Ty s) : Fu (Option (Sub Γ S T)) :=                                      -- S6a
  match leaf? S with
  | none => Fu.ret none
  | some l => Fu.firstSome (fun (sp : Path s × List Label) =>
      Fu.bind (views Γ sp.1) fun vs =>
        Fu.firstSome (fun (w : (m : Path s) × HasTy Γ (.path sp.1) (.sngl m)) =>
          match Repl.find? sp.1 w.1 S (reroot S (w.1.nomExt sp.2)) with
          | none => Fu.ret none
          | some ρ => bindO (firstView Γ w.1) fun u =>
              mapO (r (.sub (reroot S (w.1.nomExt sp.2)) T)) fun e =>
                .subtyp_trans (.subtyp_sngl_pq w.2 u.2 ρ) e) (sngls vs)) (splits l)

/-- S6b, replacement on the right, `subtyp_trans` then `subtyp_sngl_qp`. -/
def sReplR (r : Rec Γ) (S T : Ty s) : Fu (Option (Sub Γ S T)) :=                                      -- S6b
  match leaf? T with
  | none => Fu.ret none
  | some l => Fu.firstSome (fun (sp : Path s × List Label) =>
      Fu.bind (views Γ sp.1) fun vs =>
        Fu.firstSome (fun (w : (m : Path s) × HasTy Γ (.path sp.1) (.sngl m)) =>
          match Repl.find? w.1 sp.1 (reroot T (w.1.nomExt sp.2)) T with
          | none => Fu.ret none
          | some ρ => bindO (firstView Γ w.1) fun u =>
              mapO (r (.sub S (reroot T (w.1.nomExt sp.2)))) fun e =>
                .subtyp_trans e (.subtyp_sngl_qp w.2 u.2 ρ)) (sngls vs)) (splits l)

/-- S6c, one occurrence in a `μ` pair, `subtyp_sngl_pq` or `subtyp_sngl_qp` then `subtyp_trans`. -/
def sReplMu (r : Rec Γ) : (S T : Ty s) → Fu (Option (Sub Γ S T))                                     -- S6c
  | .mu S', .mu T' =>
      match Ty.firstDiff? S' T' PRename.unsucc with
      | none => Fu.ret none
      | some (l, r', S₁') =>
          Fu.firstSome (fun (pq : Path s × Path s) =>
            match Repl.find? pq.1 pq.2 (.mu S') (.mu S₁') with
            | none => Fu.ret none
            | some ρ =>
              Fu.orElse
                (bindO (viewAt Γ pq.1 (.sngl pq.2)) fun d => bindO (firstView Γ pq.2) fun u =>      -- l₀ : r₀.type
                  mapO (r (.sub (.mu S₁') (.mu T'))) fun e => .subtyp_trans (.subtyp_sngl_pq d u.2 ρ) e)
                (fun _ => bindO (viewAt Γ pq.2 (.sngl pq.1)) fun d => bindO (firstView Γ pq.1) fun u => -- r₀ : l₀.type
                  mapO (r (.sub (.mu S₁') (.mu T'))) fun e => .subtyp_trans (.subtyp_sngl_qp d u.2 ρ) e))
            (commonSplits l r')
  | _, _ => Fu.ret none

/-- S7, a lower bound, `subtyp_trans` and `subtyp_sel2`. -/
def sSelLo (r : Rec Γ) (S : Ty s) : (T : Ty s) → Fu (Option (Sub Γ S T))                              -- S7
  | .sel q A => Fu.bind (bounds Γ q A) (Fu.firstSome fun b =>
      if b.lo = .bot then Fu.ret none
      else mapO (r (.sub S b.lo)) fun e => .subtyp_trans e (.subtyp_sel2 b.d))
  | _ => Fu.ret none

/-- S8, an upper bound, `subtyp_trans` and `subtyp_sel1`. -/
def sSelHi (r : Rec Γ) (T : Ty s) : (S : Ty s) → Fu (Option (Sub Γ S T))                              -- S8
  | .sel q A => Fu.bind (bounds Γ q A) (Fu.firstSome fun b =>
      mapO (r (.sub b.hi T)) fun e => .subtyp_trans (.subtyp_sel1 b.d) e)
  | _ => Fu.ret none

/-- S9, an operand on the left, `subtyp_trans` with `subtyp_and11` or `subtyp_and12`. -/
def sAndL (r : Rec Γ) (T : Ty s) : (S : Ty s) → Fu (Option (Sub Γ S T))                               -- S9
  | .and S₁ S₂ => Fu.orElse (mapO (r (.sub S₁ T)) fun e => .subtyp_trans .subtyp_and11 e) fun _ =>
      mapO (r (.sub S₂ T)) fun e => .subtyp_trans .subtyp_and12 e
  | _ => Fu.ret none

/-- G2, `ty_and_intro`. -/
def pAndR (r : Rec Γ) (p : Path s) : (T : Ty s) → Fu (Option (HasTy Γ (.path p) T))                   -- G2
  | .and T₁ T₂ => bindO (r (.path p T₁)) fun d₁ => mapO (r (.path p T₂)) fun d₂ => .ty_and_intro d₁ d₂
  | _ => Fu.ret none
/-- G3, `ty_rec_intro`. -/
def pMu (r : Rec Γ) (p : Path s) : (T : Ty s) → Fu (Option (HasTy Γ (.path p) T))                     -- G3
  | .mu W => mapO (r (.path p (W.substPath p))) fun d => .ty_rec_intro d
  | _ => Fu.ret none
/-- G4, `ty_sub` from a view. -/
def pSub (r : Rec Γ) (p : Path s) (T : Ty s) : Fu (Option (HasTy Γ (.path p) T)) :=                    -- G4
  Fu.bind (views Γ p) (Fu.firstSome fun v => mapO (r (.sub v.1 T)) fun e => .ty_sub v.2 e)
/-- G5, `ty_rcd_intro`. -/
def pFld (r : Rec Γ) (p : Path s) : (T : Ty s) → Fu (Option (HasTy Γ (.path p) T))                    -- G5
  | .rcd (.trm a U) => mapO (r (.path (p.sel a) U)) fun d => .ty_rcd_intro d
  | _ => Fu.ret none
/-- G6, a lower bound, `ty_sub` and `subtyp_sel2`. -/
def pSelLo (r : Rec Γ) (p : Path s) : (T : Ty s) → Fu (Option (HasTy Γ (.path p) T))                  -- G6
  | .sel q A => Fu.bind (bounds Γ q A) (Fu.firstSome fun b =>
      if b.lo = .bot then Fu.ret none
      else mapO (r (.path p b.lo)) fun d => .ty_sub d (.subtyp_sel2 b.d))
  | _ => Fu.ret none
end SubAlts

/-! ## The step, the run and the entry points -/

/-- The alternatives of `sub`, in order. -/
def subStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (rAll : RecAll Γ) (S T : Ty s) : Fu (Option (Sub Γ S T)) :=
  Fu.orElse (Fu.ret (sRefl S T)) fun _ =>                -- S1
  Fu.orElse (Fu.ret (sTop S T)) fun _ =>                 -- S2
  Fu.orElse (Fu.ret (sBot S T)) fun _ =>                 -- S3
  if isAnd T then sAndR r S T else                       -- S4, final
  Fu.orElse (sStruct r rAll S T) fun _ =>                -- S5
  Fu.orElse (sReplL r S T) fun _ =>                      -- S6a
  Fu.orElse (sReplR r S T) fun _ =>                      -- S6b
  Fu.orElse (sReplMu r S T) fun _ =>                     -- S6c
  Fu.orElse (sSelLo r S T) fun _ =>                      -- S7
  Fu.orElse (sSelHi r T S) fun _ =>                      -- S8
  sAndL r T S                                            -- S9

/-- The alternatives of `path`, in order. -/
def pathStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (p : Path s) (T : Ty s) :
    Fu (Option (HasTy Γ (.path p) T)) :=
  Fu.orElse (viewAt Γ p T) fun _ =>                      -- G1
  if isAnd T then pAndR r p T else                       -- G2, final
  Fu.orElse (pMu r p T) fun _ =>                         -- G3
  Fu.orElse (pSub r p T) fun _ =>                        -- G4
  Fu.orElse (pFld r p T) fun _ =>                        -- G5
  pSelLo r p T                                           -- G6

/-- One step of the run: the goal's alternatives over the oracle `o`. -/
def step : Step G R := fun o g =>
  match g with
  | ⟨s, Γ, .sub S T⟩ => subStep Γ (fun q => o ⟨s, Γ, q⟩) (fun S₂ T₁ T₂ => o ⟨_, Γ.cons S₂, .sub T₁ T₂⟩) S T
  | ⟨s, Γ, .path p T⟩ => pathStep Γ (fun q => o ⟨s, Γ, q⟩) p T

/-- The run of a goal, with depth the fuel left. -/
def runF (g : G) : Fu (Option (R g)) := fun t => run cost step t.left [] g t
/-- The search of `Sub Γ S T` on the tank. -/
def subF {s : Sig} (Γ : Ctx s) (S T : Ty s) : Fu (Option (Sub Γ S T)) := runF ⟨s, Γ, .sub S T⟩
/-- The search of `HasTy Γ (.path p) T` on the tank. -/
def pathF {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) : Fu (Option (HasTy Γ (.path p) T)) :=
  runF ⟨s, Γ, .path p T⟩
/-- The search of `Sub Γ S T` from a full tank of `n`. -/
def sub? {s : Sig} (Γ : Ctx s) (S T : Ty s) (n : Nat := defaultFuel) : Option (Sub Γ S T) × Tank :=
  subF Γ S T ⟨n, false⟩
/-- The search of `HasTy Γ (.path p) T` from a full tank of `n`. -/
def path? {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) (n : Nat := defaultFuel) :
    Option (HasTy Γ (.path p) T) × Tank :=
  pathF Γ p T ⟨n, false⟩

/-- An answer, tank unmarked. -/
def answered {α : Type} (r : Option α × Tank) : Bool := r.1.isSome && !r.2.out
/-- No answer, tank unmarked: a rejection by the alternatives. -/
def rejected {α : Type} (r : Option α × Tank) : Bool := r.1.isNone && !r.2.out
/-- The units a run from a full tank of `n` spent. -/
def used {α : Type} (r : Option α × Tank) (n : Nat := defaultFuel) : Nat := n - r.2.left

/-! ## Frame facts

Each alternative agrees with itself under oracles that agree. -/

section SubFrames
variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {rAll rAll' : RecAll Γ}

theorem sAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) : Agree (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _
theorem sStruct_agree (hr : ∀ q, Agree (r q) (r' q)) (hA : ∀ S₂ T₁ T₂, Agree (rAll S₂ T₁ T₂) (rAll' S₂ T₁ T₂))
    (S T : Ty s) : Agree (sStruct r rAll S T) (sStruct r' rAll' S T) := by
  unfold sStruct
  split
  all_goals first
    | exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact bindO_agree (hr _) fun _ => mapO_agree _ (hA _ _ _)
    | exact ret_agree _
theorem sReplL_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) :
    Agree (sReplL r S T) (sReplL r' S T) := by
  unfold sReplL
  split
  · exact ret_agree _
  · exact firstSome_agree (fun _ => bind_agree (Agree.refl (views_framed _ _)) fun _ =>
      firstSome_agree (fun _ => by
        split
        · exact ret_agree _
        · exact bindO_agree (Agree.refl (firstView_framed _ _)) fun _ => mapO_agree _ (hr _)) _) _
theorem sReplR_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) : Agree (sReplR r S T) (sReplR r' S T) := by
  unfold sReplR
  split
  · exact ret_agree _
  · exact firstSome_agree (fun _ => bind_agree (Agree.refl (views_framed _ _)) fun _ =>
      firstSome_agree (fun _ => by
        split
        · exact ret_agree _
        · exact bindO_agree (Agree.refl (firstView_framed _ _)) fun _ => mapO_agree _ (hr _)) _) _
theorem sReplMu_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) :
    Agree (sReplMu r S T) (sReplMu r' S T) := by
  cases S <;> cases T <;> simp only [sReplMu] <;> try exact ret_agree _
  split
  · exact ret_agree _
  · exact firstSome_agree (fun _ => by
      split
      · exact ret_agree _
      · exact orElse_agree
          (bindO_agree (Agree.refl (viewAt_framed _ _ _)) fun _ =>
            bindO_agree (Agree.refl (firstView_framed _ _)) fun _ => mapO_agree _ (hr _))
          (bindO_agree (Agree.refl (viewAt_framed _ _ _)) fun _ =>
            bindO_agree (Agree.refl (firstView_framed _ _)) fun _ => mapO_agree _ (hr _))) _
theorem sSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) : Agree (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel q A =>
    exact bind_agree (Agree.refl (bounds_framed Γ q A)) fun bs =>
      firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) bs
  | _ => exact ret_agree _
theorem sSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty s) : Agree (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel q A =>
    exact bind_agree (Agree.refl (bounds_framed Γ q A)) fun bs =>
      firstSome_agree (fun _ => mapO_agree _ (hr _)) bs
  | _ => exact ret_agree _
theorem sAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty s) : Agree (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | and S1 S2 =>
    unfold sAndL
    exact orElse_agree (mapO_agree _ (hr _)) (mapO_agree _ (hr _))
  | _ => exact ret_agree _
theorem subStep_agree (hr : ∀ q, Agree (r q) (r' q)) (hA : ∀ S₂ T₁ T₂, Agree (rAll S₂ T₁ T₂) (rAll' S₂ T₁ T₂))
    (S T : Ty s) : Agree (subStep Γ r rAll S T) (subStep Γ r' rAll' S T) := by
  unfold subStep
  exact orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    ite_agree (sAndR_agree hr S T) <|
    orElse_agree (sStruct_agree hr hA S T) <| orElse_agree (sReplL_agree hr S T) <|
    orElse_agree (sReplR_agree hr S T) <| orElse_agree (sReplMu_agree hr S T) <|
    orElse_agree (sSelLo_agree hr S T) <| orElse_agree (sSelHi_agree hr T S) (sAndL_agree hr T S)
theorem pAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T : Ty s) : Agree (pAndR r p T) (pAndR r' p T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _
theorem pMu_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T : Ty s) : Agree (pMu r p T) (pMu r' p T) := by
  cases T with
  | mu W => exact mapO_agree _ (hr _)
  | _ => exact ret_agree _
theorem pSub_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T : Ty s) : Agree (pSub r p T) (pSub r' p T) :=
  bind_agree (Agree.refl (views_framed Γ p)) fun vs => firstSome_agree (fun _ => mapO_agree _ (hr _)) vs
theorem pFld_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T : Ty s) : Agree (pFld r p T) (pFld r' p T) := by
  cases T with
  | rcd D =>
    cases D with
    | trm a U => exact mapO_agree _ (hr _)
    | typ _ _ _ => exact ret_agree _
  | _ => exact ret_agree _
theorem pSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T : Ty s) : Agree (pSelLo r p T) (pSelLo r' p T) := by
  cases T with
  | sel q A =>
    exact bind_agree (Agree.refl (bounds_framed Γ q A)) fun bs =>
      firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) bs
  | _ => exact ret_agree _
theorem pathStep_agree (hr : ∀ q, Agree (r q) (r' q)) (p : Path s) (T : Ty s) :
    Agree (pathStep Γ r p T) (pathStep Γ r' p T) := by
  unfold pathStep
  exact orElse_agree (Agree.refl (viewAt_framed Γ p T)) <| ite_agree (pAndR_agree hr p T) <|
    orElse_agree (pMu_agree hr p T) <| orElse_agree (pSub_agree hr p T) <|
    orElse_agree (pFld_agree hr p T) (pSelLo_agree hr p T)
end SubFrames

/-! ## The step and the entry points: framed, unmarked, monotone -/

theorem step_frame : FrameF step := by
  intro o o' ho g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | sub S T =>
    exact subStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rAll := fun S2 T1 T2 => o ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (rAll' := fun S2 T1 T2 => o' ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (fun q => ho ⟨s, Γ, q⟩) (fun S2 T1 T2 => ho ⟨_, Γ.cons S2, .sub T1 T2⟩) S T
  | path p T =>
    exact pathStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) p T
theorem runF_framed (g : G) : Framed (runF g) :=
  atLeft_framed fun d d' hd => run_agree step_frame d d' hd [] g
theorem subF_framed {s : Sig} (Γ : Ctx s) (S T : Ty s) : Framed (subF Γ S T) :=
  runF_framed _
theorem pathF_framed {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) : Framed (pathF Γ p T) :=
  runF_framed _

/-- An answer of `c` leaves the tank unmarked. -/
def Unmarked {α : Type} (c : Fu (Option α)) : Prop :=
  ∀ t, (c t).1.isSome = true → (c t).2.out = false
theorem run_some {G : Type} [DecidableEq G] {R : G → Type} {cost : Nat → Nat} {F : Step G R}
    {d : Nat} {P : List G} {g : G} {t : Tank} {x : R g}
    (h : (run cost F d P g t).1 = some x) : (run cost F d P g t).2.out = false := by
  cases d with
  | zero => simp [run] at h
  | succ d =>
    rw [run_succ] at h ⊢
    exact node_some (k := F (run cost F d (g :: P)) g) (Prod.ext h rfl)
theorem run_unmarked {G : Type} [DecidableEq G] {R : G → Type} {cost : Nat → Nat} {F : Step G R}
    (d : Nat) (P : List G) (g : G) : Unmarked (run cost F d P g) := by
  intro t h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  exact run_some hx
theorem runF_unmarked (g : G) : Unmarked (runF g) := fun t => run_unmarked t.left [] g t
theorem subF_unmarked {s : Sig} (Γ : Ctx s) (S T : Ty s) : Unmarked (subF Γ S T) :=
  runF_unmarked _
theorem pathF_unmarked {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) : Unmarked (pathF Γ p T) :=
  runF_unmarked _

theorem full_add {n m : Nat} (h : n ≤ m) : (⟨n, false⟩ : Tank).add (m - n) = ⟨m, false⟩ := by
  simp only [Tank.add, Tank.mk.injEq, and_true]
  omega
theorem full_mono {α : Type} {c : Fu (Option α)} (hF : Framed c) (hU : Unmarked c) {n m : Nat}
    {e : α} (h : (c ⟨n, false⟩).1 = some e) (hnm : n ≤ m) : (c ⟨m, false⟩).1 = some e := by
  have ho : (c ⟨n, false⟩).2.out = false := hU _ (by simp [h])
  have := hF.shift ⟨n, false⟩ (some e) _ (Prod.ext h rfl) ho (m - n)
  rw [full_add hnm] at this
  rw [this]
theorem sub?_mono {s : Sig} {Γ : Ctx s} {S T : Ty s} {n m : Nat} {e : Sub Γ S T}
    (h : (sub? Γ S T n).1 = some e) (hnm : n ≤ m) : (sub? Γ S T m).1 = some e :=
  full_mono (subF_framed Γ S T) (subF_unmarked Γ S T) h hnm
theorem path?_mono {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s} {n m : Nat} {e : HasTy Γ (.path p) T}
    (h : (path? Γ p T n).1 = some e) (hnm : n ≤ m) : (path? Γ p T m).1 = some e :=
  full_mono (pathF_framed Γ p T) (pathF_unmarked Γ p T) h hnm
theorem answered_isSome {α : Type} {r : Option α × Tank} (h : answered r = true) :
    r.1.isSome = true ∧ r.2.out = false := by
  simpa [answered] using h

/-! ## Tests

`⊥ <: ⊤` is answered and `⊤ <: ⊥` rejected, both with the tank unmarked.  The
splits of a path and the common splits of two paths.  S6c's reading on E10:
the bodies `{a : p.type} ∧ {b : p.type}` and `{a : q.type} ∧ {b : q.type}`
under one binder first differ at `a`, read back to `p` and `q`, and the left
body with that one path replaced is `{a : q.type} ∧ {b : p.type}`. -/

section Tests
open Nominal.Source (e10_p e10_q e10_ty)

example : answered (sub? (s := []) Ctx.nil .bot .top) = true := by decide +kernel
example : rejected (sub? (s := []) Ctx.nil .top .bot) = true := by decide +kernel
example : splits (s := ([],x)) (((Path.var .here).sel (.trm 0)).sel (.trm 1)) =
    [(((Path.var .here).sel (.trm 0)).sel (.trm 1), []), ((Path.var .here).sel (.trm 0), [.trm 1]),
     (.var .here, [.trm 0, .trm 1])] := by decide +kernel
example : commonSplits (s := (([],x),x)) (((Path.var .here).sel (.trm 0)).sel (.trm 1))
    (((Path.var (.there .here)).sel (.trm 2)).sel (.trm 1)) =
    [(((Path.var .here).sel (.trm 0)).sel (.trm 1), ((Path.var (.there .here)).sel (.trm 2)).sel (.trm 1)),
     ((Path.var .here).sel (.trm 0), (Path.var (.there .here)).sel (.trm 2))] := by decide +kernel
example : Ty.firstDiff? (e10_ty e10_p e10_p).weaken (e10_ty e10_q e10_q).weaken PRename.unsucc =
    some (e10_p, e10_q, (e10_ty e10_q e10_p).weaken) := by decide +kernel
end Tests

/-! ## Checks

The acceptance programs of stage XF1 of plan XI
(`plan-11-pdot-frontends.md:1245-1249`): E9, the four types of E10, E11 at
`⊤` and at `{B : ⊥..⊤}`, N4 with no answer, replacement by PQ and QP, `μ`
pairs by S6c, and the chain R14Chain12, which is the stage's risk.  Then one
check per alternative that no check before it reaches.  Each check reads
`answered` or `rejected`, so the tank is unmarked in each.  The comment beside
a check gives the units it used in the prototype. -/

section Checks
open Nominal.Source (e9_G e9_x e9_a e9_b e10_G e10_r e10_p e10_q e10_ty e11_G e11_p e11_a n4_G)

-- E9 (PDot/Source/Examples.lean:35-76): x.a.b : ⊤ and x.a.b : (x.b).type                         20, 20 units
example : answered (path? e9_G ((e9_x.sel e9_a).sel e9_b) .top) = true := by decide +kernel
example : answered (path? e9_G ((e9_x.sel e9_a).sel e9_b) (.sngl (e9_x.sel e9_b))) = true := by decide +kernel
-- E10 (:78-136): the four types of r                                                                2, 35, 58, 31
example : answered (path? e10_G e10_r (e10_ty e10_p e10_p)) = true := by decide +kernel
example : answered (path? e10_G e10_r (e10_ty e10_p e10_q)) = true := by decide +kernel
example : answered (path? e10_G e10_r (e10_ty e10_q e10_q)) = true := by decide +kernel
example : answered (path? e10_G e10_r (e10_ty e10_q e10_p)) = true := by decide +kernel
-- E11 (:138-173) at T = ⊤: p : {a : T}                                                               10
example : answered (path? (e11_G .top) e11_p (.rcd (.trm e11_a Ty.top.weaken.weaken))) = true := by decide +kernel
-- E11 at T = {B : ⊥..⊤}: the answer runs G5 (ty_rcd_intro) and ty_sngl, which ⊤ skips by S2         18
example : answered (path? (e11_G (.rcd (.typ (.typ 0) .bot .top))) e11_p
    (.rcd (.trm e11_a (Ty.rcd (.typ (.typ 0) .bot .top)).weaken.weaken))) = true := by decide +kernel
-- N4 (:425-526): x : x.type has no answer, tank unmarked                                            6
example : rejected (path? (n4_G (.typ 0)) (.var .here) (.sngl (.var .here))) = true := by decide +kernel

/-- `q : {B : ⊥..⊤}`, `p : q.type`. -/
abbrev pqB : Label := .typ 0
abbrev pqG : Ctx (([],x),x) := (Ctx.nil.cons (.rcd (.typ pqB .bot .top))).cons (.sngl (.var .here))
abbrev pqP : Path (([],x),x) := .var .here
abbrev pqQ : Path (([],x),x) := .var (.there .here)
-- PQ (S6a) and QP (S6b), d3's sc/A04ReplPQ and sc/A05ReplQP                                          7, 8
example : answered (sub? pqG (.sel pqP pqB) (.sel pqQ pqB)) = true := by decide +kernel
example : answered (sub? pqG (.sel pqQ pqB) (.sel pqP pqB)) = true := by decide +kernel

/-- `q : ⊤`, `p : q.type`.  In a `μ` body at `(([],x),x),x`, `p` is `.there .here` and `q` is `.there (.there .here)`. -/
abbrev muA : Label := .trm 0
abbrev muB : Label := .trm 1
abbrev muG : Ctx (([],x),x) := (Ctx.nil.cons .top).cons (.sngl (.var .here))
abbrev muP : Path ((([],x),x),x) := .var (.there .here)
abbrev muQ : Path ((([],x),x),x) := .var (.there (.there .here))
-- μ pairs (S6c): one occurrence by pq, one by qp, two occurrences one at a time, and a pair with no replacement   7, 8, 14, 1
example : answered (sub? muG (.mu (.rcd (.trm muA (.sngl muP)))) (.mu (.rcd (.trm muA (.sngl muQ))))) = true := by decide +kernel
example : answered (sub? muG (.mu (.rcd (.trm muA (.sngl muQ)))) (.mu (.rcd (.trm muA (.sngl muP))))) = true := by decide +kernel
example : answered (sub? muG (.mu (.and (.rcd (.trm muA (.sngl muP))) (.rcd (.trm muB (.sngl muP)))))
    (.mu (.and (.rcd (.trm muA (.sngl muQ))) (.rcd (.trm muB (.sngl muQ)))))) = true := by decide +kernel
example : rejected (sub? muG (.mu (.rcd (.trm muA .top))) (.mu (.rcd (.trm muA .bot)))) = true := by decide +kernel

/-- A signature of `k` variables. -/
def sigN : Nat → Sig
  | 0 => []
  | n + 1 => (sigN n),x
abbrev chA : Label := .trm 0
abbrev chB : Label := .typ 0
/-- refute-d3's R14Chain: `x0 : {B : ⊥..⊤}`, `x1 : {a : x0.type}`, `xk : {a : x(k-1).a.type}` up to `x(n+1)`. -/
def chainG : (n : Nat) → Ctx (sigN (n + 2))
  | 0 => (Ctx.nil.cons (.rcd (.typ chB .bot .top))).cons (.rcd (.trm chA (.sngl (.var .here))))
  | n + 1 => (chainG n).cons (.rcd (.trm chA (.sngl (.sel (.var .here) chA))))
/-- `x0`, seen from the end of the chain. -/
def chainX0 : (n : Nat) → BVar (sigN (n + 2)) .var
  | 0 => .there .here
  | n + 1 => .there (chainX0 n)
/-- `x(n+1).a.B <: x0.B`, the goal of R14Chain at `n + 1` links. -/
def chainGoal (n : Nat) : Option (Sub (chainG n) (.sel (.sel (.var .here) chA) chB) (.sel (.var (chainX0 n)) chB)) × Tank :=
  sub? (chainG n) (.sel (.sel (.var .here) chA) chB) (.sel (.var (chainX0 n)) chB)
-- R14Chain12, the stage's risk                                                                       1703
example : answered (chainGoal 11) = true ∧ used (chainGoal 11) ≤ 4096 := by decide +kernel

/-! The alternatives that no check above reaches, one check each (refutation R2). -/
abbrev xA : Label := .typ 0
abbrev xa : Label := .trm 0
/-- `x : {A : {a : ⊤}..⊤}`, `y : {a : ⊤}`. -/
abbrev loG : Ctx (([],x),x) := (Ctx.nil.cons (.rcd (.typ xA (.rcd (.trm xa .top)) .top))).cons (.rcd (.trm xa .top))
abbrev loX : Path (([],x),x) := .var (.there .here)
abbrev loY : Path (([],x),x) := .var .here
/-- `x : {A : ⊥..{a : ⊤}}`. -/
abbrev hiG : Ctx ([],x) := Ctx.nil.cons (.rcd (.typ xA .bot (.rcd (.trm xa .top))))
/-- `∀(z : {A : ⊥..{a : ⊤}}) z.A` and `∀(z : {A : ⊥..{a : ⊤}}) {a : ⊤}`. -/
abbrev allS : Ty [] := .all (.rcd (.typ xA .bot (.rcd (.trm xa .top)))) (.sel (.var .here) xA)
abbrev allT : Ty [] := .all (.rcd (.typ xA .bot (.rcd (.trm xa .top)))) (.rcd (.trm xa .top))
-- G3, then G4 and S9: x : μ(z. {b : ⊤}) in E9                                                       5
example : answered (path? e9_G e9_x (.mu (.rcd (.trm e9_b .top)))) = true := by decide +kernel
-- y : x.A by the lower bound {a : ⊤}, answered by G4 then S7 (subtyp_sel2 on a path goal)            10
example : answered (path? loG loY (.sel loX xA)) = true := by decide +kernel
-- S7: {a : ⊤} <: x.A                                                                                 5
example : answered (sub? loG (.rcd (.trm xa .top)) (.sel loX xA)) = true := by decide +kernel
-- S8: x.A <: {a : ⊤}                                                                                 5
example : answered (sub? hiG (.sel (.var .here) xA) (.rcd (.trm xa .top))) = true := by decide +kernel
-- S5 at type members: {A : ⊥..{a : ⊤}} <: {A : ⊥..⊤}                                                5
example : answered (sub? (s := []) Ctx.nil (.rcd (.typ xA .bot (.rcd (.trm xa .top)))) (.rcd (.typ xA .bot .top))) = true := by decide +kernel
-- S5 at ∀: the codomains under z : S₂, where z.A <: {a : ⊤} needs the new binder's bound (S8)       10
example : answered (sub? Ctx.nil allS allT) = true := by decide +kernel
-- S9: {a : ⊤} ∧ {b : ⊥} <: {b : ⊥} by the right operand                                            5
example : answered (sub? (s := []) Ctx.nil (.and (.rcd (.trm xa .top)) (.rcd (.trm (.trm 1) .bot))) (.rcd (.trm (.trm 1) .bot))) = true := by decide +kernel
end Checks

end NominalFrontend.Core
