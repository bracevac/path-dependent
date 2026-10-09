import Coercions.Paths.DotMNF.Syntax

/-!
# Annotated DOT-MNF terms with paths

`ATm` is `Paths.DotMNF.Tm` with two extra fields: the self type of an object
literal and the optional result type of a `let`.

The self type must be carried because `HasTy.obj` checks the definitions of a
literal against a context entry that already holds it.  It cannot be
synthesized from the definitions.  `Value.obj` has no slot for it, so the
annotation lives in the front end's own syntax.  The `let` type is optional
because an unannotated `let` has its type strengthened or widened to `⊤` by the
typer.

The path term takes a variable.  A deeper path in term position is written
with a `let` per prefix, which `Resolve.lean` inserts.

A partial term `PTm` is an `ATm` whose slots may be empty: a lambda's domain,
a literal's self type, and a written field type.  The resolver returns one, and
the elaborator fills its slots.  `ATm` is the elaborated term, the input of the
typer and of `ATm.erase`, so the typer never sees an empty slot.

`ATm.erase` drops the annotations and gives back a `Tm`.  Nothing here is part
of the metatheory.  The size functions count nodes and are positive, so a
walker can take a fuel from them that is never zero.  Every recursive
definition uses `termination_by structural`.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Ty Tm Defs)

/-! ## The syntax -/

mutual
/-- Terms of DOT-MNF with paths and the two annotations.  Application,
projection and the path term take variables, so the terms are in monadic normal
form by construction. -/
inductive ATm : Sig → Type where
  /-- A variable.  A deeper path in term position is a chain of `let`s. -/
  | path : BVar s .var → ATm s
  /-- `λ(x : T). t`. -/
  | lam : Ty s → ATm (s,x) → ATm s
  /-- `ν(x : T. d)`, the self type annotated. -/
  | obj : Ty (s,x) → ADefs (s,x) → ATm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → ATm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → ATm s
  /-- `let x (: U)? = t in u`. -/
  | «let» : Option (Ty s) → ATm s → ATm (s,x) → ATm s
/-- Definitions of an annotated object literal. -/
inductive ADefs : Sig → Type where
  /-- `{type A = T}`. -/
  | typ : Label → Ty s → ADefs s
  /-- `{a = t}`. -/
  | trm : Label → ATm s → ADefs s
  /-- `d ∧ e`. -/
  | and : ADefs s → ADefs s → ADefs s
end

deriving instance DecidableEq for ATm, ADefs

/-! ## Erasure

Erasure drops the annotations and changes nothing else. -/

mutual
/-- Drop the annotations of a term. -/
def ATm.erase : {s : Sig} → ATm s → Tm s
  | _, .path x => .path x
  | _, .lam T t => .val (.lam T t.erase)
  | _, .obj _ d => .val (.obj d.erase)
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let _ t u => .let t.erase u.erase
termination_by structural _ t => t
/-- Drop the annotations of a definition list. -/
def ADefs.erase : {s : Sig} → ADefs s → Defs s
  | _, .typ A T => .typ A T
  | _, .trm a t => .trm a t.erase
  | _, .and d e => .and d.erase e.erase
termination_by structural _ d => d
end

/-! ## Renaming

As `Paths.DotMNF.Tm.rename`.  The self type of a literal is under the self
binder and takes the lifted renaming.  The type of a `let` is outside its
binder and takes the renaming itself. -/

mutual
/-- Rename the free variables of an annotated term. -/
def ATm.rename : {s1 s2 : Sig} → ATm s1 → Rename s1 s2 → ATm s2
  | _, _, .path x, ρ => .path (ρ.var x)
  | _, _, .lam T t, ρ => .lam (T.rename ρ) (t.rename ρ.lift)
  | _, _, .obj T d, ρ => .obj (T.rename ρ.lift) (d.rename ρ.lift)
  | _, _, .app x y, ρ => .app (ρ.var x) (ρ.var y)
  | _, _, .proj x a, ρ => .proj (ρ.var x) a
  | _, _, .let ann t u, ρ =>
      .let (ann.map (fun U => U.rename ρ)) (t.rename ρ) (u.rename ρ.lift)
termination_by structural _ _ t => t
/-- Rename the free variables of an annotated definition list. -/
def ADefs.rename : {s1 s2 : Sig} → ADefs s1 → Rename s1 s2 → ADefs s2
  | _, _, .typ A T, ρ => .typ A (T.rename ρ)
  | _, _, .trm a t, ρ => .trm a (t.rename ρ)
  | _, _, .and d e, ρ => .and (d.rename ρ) (e.rename ρ)
termination_by structural _ _ d => d
end

/-- Weakening of an annotated term, under one new binder. -/
def ATm.weaken (t : ATm s) : ATm (s,x) := t.rename Rename.succ

/-! ## Erasure commutes with renaming -/

mutual
/-- Erasure commutes with renaming. -/
theorem ATm.erase_rename : ∀ {s1 s2 : Sig} (t : ATm s1) (ρ : Rename s1 s2),
    (t.rename ρ).erase = t.erase.rename ρ
  | _, _, .path _, _ => rfl
  | _, _, .lam T t, ρ => by
      show Tm.val (.lam (T.rename ρ) (t.rename ρ.lift).erase) = _
      rw [ATm.erase_rename t ρ.lift]; rfl
  | _, _, .obj _ d, ρ => by
      show Tm.val (.obj (d.rename ρ.lift).erase) = _
      rw [ADefs.erase_rename d ρ.lift]; rfl
  | _, _, .app _ _, _ => rfl
  | _, _, .proj _ _, _ => rfl
  | _, _, .let _ t u, ρ => by
      show Tm.let (t.rename ρ).erase (u.rename ρ.lift).erase = _
      rw [ATm.erase_rename t ρ, ATm.erase_rename u ρ.lift]; rfl
/-- Erasure commutes with renaming, on definitions. -/
theorem ADefs.erase_rename : ∀ {s1 s2 : Sig} (d : ADefs s1) (ρ : Rename s1 s2),
    (d.rename ρ).erase = d.erase.rename ρ
  | _, _, .typ _ _, _ => rfl
  | _, _, .trm a t, ρ => by
      show Defs.trm a (t.rename ρ).erase = _
      rw [ATm.erase_rename t ρ]; rfl
  | _, _, .and d e, ρ => by
      show Defs.and (d.rename ρ).erase (e.rename ρ).erase = _
      rw [ADefs.erase_rename d ρ, ADefs.erase_rename e ρ]; rfl
end

/-! ## Size

The node count of a term.  Types do not count. -/

mutual
/-- The node count of an annotated term. -/
def sizeATm : {s : Sig} → ATm s → Nat
  | _, .path _ => 1
  | _, .lam _ t => sizeATm t + 1
  | _, .obj _ d => sizeADefs d + 1
  | _, .app _ _ => 1
  | _, .proj _ _ => 1
  | _, .let _ t u => sizeATm t + sizeATm u + 1
termination_by structural _ t => t
/-- The node count of an annotated definition list. -/
def sizeADefs : {s : Sig} → ADefs s → Nat
  | _, .typ _ _ => 1
  | _, .trm _ t => sizeATm t + 1
  | _, .and d e => sizeADefs d + sizeADefs e + 1
termination_by structural _ d => d
end

mutual
/-- Every term has at least one node. -/
theorem sizeATm_pos : ∀ {s : Sig} (t : ATm s), 0 < sizeATm t
  | _, .path _ => Nat.zero_lt_one
  | _, .lam _ _ => Nat.succ_pos _
  | _, .obj _ _ => Nat.succ_pos _
  | _, .app _ _ => Nat.zero_lt_one
  | _, .proj _ _ => Nat.zero_lt_one
  | _, .let _ _ _ => Nat.succ_pos _
/-- Every definition list has at least one node. -/
theorem sizeADefs_pos : ∀ {s : Sig} (d : ADefs s), 0 < sizeADefs d
  | _, .typ _ _ => Nat.zero_lt_one
  | _, .trm _ _ => Nat.succ_pos _
  | _, .and _ _ => Nat.succ_pos _
end

/-- The body of a term member is smaller than the definition list. -/
theorem sizeATm_lt_trm {s : Sig} (a : Label) (t : ATm s) :
    sizeATm t < sizeADefs (.trm a t) := Nat.lt_succ_self _

/-- The bound term of a `let` is smaller than the `let`. -/
theorem sizeATm_lt_letBound {s : Sig} (ann : Option (Ty s)) (t : ATm s) (u : ATm (s,x)) :
    sizeATm t < sizeATm (.let ann t u) := by
  show sizeATm t < sizeATm t + sizeATm u + 1
  omega

/-- The body of a `let` is smaller than the `let`. -/
theorem sizeATm_lt_letBody {s : Sig} (ann : Option (Ty s)) (t : ATm s) (u : ATm (s,x)) :
    sizeATm u < sizeATm (.let ann t u) := by
  show sizeATm u < sizeATm t + sizeATm u + 1
  omega

/-! ## Partial terms

`PTm` is `ATm` with `Option` at every slot inference may fill: a lambda's
domain, a literal's self type, and a written field type.  `none` is an empty
slot.  The resolver returns a `PTm`, the elaborator fills it, and the elaborated
term is an `ATm`, the input of the typer.  Each `let` also records where it
comes from, since the elaborator treats a call argument apart from other
bindings. -/

/-- Where a `let` of a partial term comes from.  `written` is a `let` of the
source.  `arg` is the binding `atomize` inserts at the operand of an
application, the one place a call argument sits.  `recv` is the binding at an
operator or at the receiver of a projection.  `asc` is an ascription. -/
inductive LetTag where
  | written
  | arg
  | recv
  | asc
deriving DecidableEq, Repr

mutual
/-- An annotated term whose slots may be empty. -/
inductive PTm : Sig → Type where
  /-- A variable. -/
  | path : BVar s .var → PTm s
  /-- `λ(x : T). t`, or `λx. t` with the domain empty. -/
  | lam : Option (Ty s) → PTm (s,x) → PTm s
  /-- `ν(x : T. d)`, or `ν(x. d)` with the self type empty. -/
  | obj : Option (Ty (s,x)) → PDefs (s,x) → PTm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → PTm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → PTm s
  /-- `let x (: U)? = t in u`, with the origin of the binding. -/
  | «let» : LetTag → Option (Ty s) → PTm s → PTm (s,x) → PTm s
/-- Definitions whose term members may carry a written type. -/
inductive PDefs : Sig → Type where
  /-- `{type A = T}`. -/
  | typ : Label → Ty s → PDefs s
  /-- `{a = t}`, or `{a : T = t}` with a written type. -/
  | trm : Label → Option (Ty s) → PTm s → PDefs s
  /-- `d ∧ e`. -/
  | and : PDefs s → PDefs s → PDefs s
end

deriving instance DecidableEq for PTm, PDefs

/-! ## The bridges to `ATm` -/

mutual
/-- The `ATm` a partial term stands for, when no slot is empty.  A written
field type has no place in `ATm`, so it makes the term partial.  The tag is
dropped. -/
def PTm.full? : {s : Sig} → PTm s → Option (ATm s)
  | _, .path x => some (.path x)
  | _, .lam (some S) t => t.full?.map (.lam S)
  | _, .lam none _ => none
  | _, .obj (some T) d => d.full?.map (.obj T)
  | _, .obj none _ => none
  | _, .app x y => some (.app x y)
  | _, .proj x a => some (.proj x a)
  | _, .let _ ann t u =>
      match t.full?, u.full? with
      | some a, some b => some (.let ann a b)
      | _, _ => none
termination_by structural _ t => t
/-- The `ADefs` that the definitions of a partial term stand for, when no slot
is empty and no field type is written. -/
def PDefs.full? : {s : Sig} → PDefs s → Option (ADefs s)
  | _, .typ A T => some (.typ A T)
  | _, .trm a none t => t.full?.map (.trm a)
  | _, .trm _ (some _) _ => none
  | _, .and d e =>
      match d.full?, e.full? with
      | some a, some b => some (.and a b)
      | _, _ => none
termination_by structural _ d => d
end

mutual
/-- Every slot written.  Every `let` is tagged `written`. -/
def ATm.toI : {s : Sig} → ATm s → PTm s
  | _, .path x => .path x
  | _, .lam S t => .lam (some S) t.toI
  | _, .obj T d => .obj (some T) d.toI
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let ann t u => .let .written ann t.toI u.toI
termination_by structural _ t => t
/-- Every slot written, and no field type. -/
def ADefs.toI : {s : Sig} → ADefs s → PDefs s
  | _, .typ A T => .typ A T
  | _, .trm a t => .trm a none t.toI
  | _, .and d e => .and d.toI e.toI
termination_by structural _ d => d
end

/-! ## Agreement with the written slots -/

/-- The left part of an intersection.  Any other type gives `⊤`, which has no
field, so a written field type checked against it does not agree. -/
def andLeft {s : Sig} : Ty s → Ty s
  | .and T _ => T
  | _ => .top

/-- The right part of an intersection, and `⊤` for any other type. -/
def andRight {s : Sig} : Ty s → Ty s
  | .and _ T => T
  | _ => .top

mutual
/-- The elaborated term agrees with every written slot.  An empty slot agrees
with anything.  The tag is ignored. -/
def PTm.fills : {s : Sig} → PTm s → ATm s → Bool
  | _, .path x, .path y => decide (x = y)
  | _, .lam o t, .lam S a =>
      (match o with | some S' => decide (S' = S) | none => true) && t.fills a
  | _, .obj o d, .obj T d' =>
      (match o with | some T' => decide (T' = T) | none => true) && d.fills T d'
  | _, .app x y, .app x' y' => decide (x = x') && decide (y = y')
  | _, .proj x a, .proj x' a' => decide (x = x') && decide (a = a')
  | _, .let _ o t u, .let o' a b => decide (o = o') && t.fills a && u.fills b
  | _, _, _ => false
termination_by structural _ t => t
/-- Definitions against the self type they were typed at, in lockstep.  A
written field type equals the self type's field at that label.  It agrees with
a plain field `{a : T}` only, since a field with a written type is no stable
member.  An intersection of definitions splits the self type with `andLeft`
and `andRight`, so a self type out of step with the definitions leaves no field
for a written type to agree with. -/
def PDefs.fills : {s : Sig} → PDefs s → Ty s → ADefs s → Bool
  | _, .typ A T, _, .typ A' T' => decide (A = A') && decide (T = T')
  | _, .trm a o t, U, .trm a' b =>
      decide (a = a') &&
      (match o, U with
       | some V, .fld _ W => decide (V = W)
       | some _, _ => false
       | none, _ => true) && t.fills b
  | _, .and d e, U, .and d' e' => d.fills (andLeft U) d' && e.fills (andRight U) e'
  | _, _, _, _ => false
termination_by structural _ d => d
end

/-! ## The size measure of partial terms

The same node count as `sizeATm` and `sizeADefs`.  Types and tags do not
count. -/

mutual
/-- The node count of a partial term. -/
def sizePTm : {s : Sig} → PTm s → Nat
  | _, .path _ => 1
  | _, .lam _ t => sizePTm t + 1
  | _, .obj _ d => sizePDefs d + 1
  | _, .app _ _ => 1
  | _, .proj _ _ => 1
  | _, .let _ _ t u => sizePTm t + sizePTm u + 1
termination_by structural _ t => t
/-- The node count of the definitions of a partial term. -/
def sizePDefs : {s : Sig} → PDefs s → Nat
  | _, .typ _ _ => 1
  | _, .trm _ _ t => sizePTm t + 1
  | _, .and d e => sizePDefs d + sizePDefs e + 1
termination_by structural _ d => d
end

/-! ## Erasures

Each erasure maps a partial term to a partial term with some written slots
emptied.  They state that a program written with fewer annotations resolves to
the written program with those annotations erased. -/

/-- Erase a lambda's domain, at the head only. -/
def PTm.dropDom : {s : Sig} → PTm s → PTm s
  | _, .lam _ t => .lam none t
  | _, t => t

mutual
/-- Every lambda domain erased. -/
def PTm.eraseDoms : {s : Sig} → PTm s → PTm s
  | _, .path x => .path x
  | _, .lam _ t => .lam none t.eraseDoms
  | _, .obj T d => .obj T d.eraseDoms
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let g ann t u => .let g ann t.eraseDoms u.eraseDoms
termination_by structural _ t => t
/-- Every lambda domain erased, in definitions. -/
def PDefs.eraseDoms : {s : Sig} → PDefs s → PDefs s
  | _, .typ A T => .typ A T
  | _, .trm a o t => .trm a o t.eraseDoms
  | _, .and d e => .and d.eraseDoms e.eraseDoms
termination_by structural _ d => d
end

mutual
/-- Every self type erased. -/
def PTm.eraseSelf : {s : Sig} → PTm s → PTm s
  | _, .path x => .path x
  | _, .lam S t => .lam S t.eraseSelf
  | _, .obj _ d => .obj none d.eraseSelf
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let g ann t u => .let g ann t.eraseSelf u.eraseSelf
termination_by structural _ t => t
/-- Every self type erased, in definitions. -/
def PDefs.eraseSelf : {s : Sig} → PDefs s → PDefs s
  | _, .typ A T => .typ A T
  | _, .trm a o t => .trm a o t.eraseSelf
  | _, .and d e => .and d.eraseSelf e.eraseSelf
termination_by structural _ d => d
end

mutual
/-- The domain of every lambda bound by an `arg` binding erased. -/
def PTm.eraseArgs : {s : Sig} → PTm s → PTm s
  | _, .path x => .path x
  | _, .lam S t => .lam S t.eraseArgs
  | _, .obj T d => .obj T d.eraseArgs
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let g ann t u =>
      .let g ann (if g = .arg then t.eraseArgs.dropDom else t.eraseArgs) u.eraseArgs
termination_by structural _ t => t
/-- The domain of every lambda bound by an `arg` binding erased, in
definitions. -/
def PDefs.eraseArgs : {s : Sig} → PDefs s → PDefs s
  | _, .typ A T => .typ A T
  | _, .trm a o t => .trm a o t.eraseArgs
  | _, .and d e => .and d.eraseArgs e.eraseArgs
termination_by structural _ d => d
end

/-! ## The bridges agree -/

mutual
/-- A term with every slot written is full, and `full?` gives it back. -/
theorem ATm.full?_toI : ∀ {s : Sig} (a : ATm s), a.toI.full? = some a
  | _, .path _ => rfl
  | _, .lam S t => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, Option.map_some]
  | _, .obj T d => by simp only [ATm.toI, PTm.full?, ADefs.full?_toI d, Option.map_some]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let ann t u => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, ATm.full?_toI u]
/-- Definitions with every slot written are full, and `full?` gives them
back. -/
theorem ADefs.full?_toI : ∀ {s : Sig} (d : ADefs s), d.toI.full? = some d
  | _, .typ _ _ => rfl
  | _, .trm a t => by simp only [ADefs.toI, PDefs.full?, ATm.full?_toI t, Option.map_some]
  | _, .and d e => by simp only [ADefs.toI, PDefs.full?, ADefs.full?_toI d, ADefs.full?_toI e]
end

mutual
/-- A term with every slot written agrees with itself. -/
theorem ATm.fills_toI : ∀ {s : Sig} (a : ATm s), a.toI.fills a = true
  | _, .path _ => by simp only [ATm.toI, PTm.fills, decide_true]
  | _, .lam _ t => by simp only [ATm.toI, PTm.fills, decide_true, Bool.true_and, ATm.fills_toI t]
  | _, .obj T d => by
      simp only [ATm.toI, PTm.fills, decide_true, Bool.true_and, ADefs.fills_toI d T]
  | _, .app _ _ => by simp only [ATm.toI, PTm.fills, decide_true, Bool.and_self]
  | _, .proj _ _ => by simp only [ATm.toI, PTm.fills, decide_true, Bool.and_self]
  | _, .let _ t u => by
      simp only [ATm.toI, PTm.fills, decide_true, ATm.fills_toI t, ATm.fills_toI u,
        Bool.and_self]
/-- Definitions with every slot written agree with themselves, against any
self type, since they carry no written field type. -/
theorem ADefs.fills_toI : ∀ {s : Sig} (d : ADefs s) (T : Ty s), d.toI.fills T d = true
  | _, .typ _ _, _ => by simp only [ADefs.toI, PDefs.fills, decide_true, Bool.and_self]
  | _, .trm _ t, _ => by
      simp only [ADefs.toI, PDefs.fills, decide_true, ATm.fills_toI t, Bool.and_self]
  | _, .and d e, T => by
      simp only [ADefs.toI, PDefs.fills, ADefs.fills_toI d (andLeft T),
        ADefs.fills_toI e (andRight T), Bool.and_self]
end

mutual
/-- A full partial term agrees with the term it gives. -/
theorem PTm.fills_of_full? : ∀ {s : Sig} {p : PTm s} {a : ATm s},
    p.full? = some a → p.fills a = true
  | _, .path _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true]
  | _, .lam (some _) t, _, h => by
      simp only [PTm.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PTm.fills, decide_true, Bool.true_and, PTm.fills_of_full? ht]
  | _, .lam none _, _, h => by simp only [PTm.full?, reduceCtorEq] at h
  | _, .obj (some T) d, _, h => by
      simp only [PTm.full?] at h
      cases hd : d.full? with
      | none => simp only [hd, Option.map_none, reduceCtorEq] at h
      | some e =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PTm.fills, decide_true, Bool.true_and, PDefs.fills_of_full? T hd]
  | _, .obj none _, _, h => by simp only [PTm.full?, reduceCtorEq] at h
  | _, .app _ _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true, Bool.and_self]
  | _, .proj _ _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true, Bool.and_self]
  | _, .let _ _ t u, _, h => by
      simp only [PTm.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, reduceCtorEq] at h
      | some b =>
          cases hu : u.full? with
          | none => simp only [ht, hu, reduceCtorEq] at h
          | some c =>
              simp only [ht, hu, Option.some.injEq] at h
              subst h
              simp only [PTm.fills, decide_true, PTm.fills_of_full? ht, PTm.fills_of_full? hu,
                Bool.and_self]
/-- Full `PDefs` agree with the definitions they give, against any self
type. -/
theorem PDefs.fills_of_full? : ∀ {s : Sig} {d : PDefs s} {e : ADefs s} (T : Ty s),
    d.full? = some e → d.fills T e = true
  | _, .typ _ _, _, _, h => by
      simp only [PDefs.full?, Option.some.injEq] at h
      subst h
      simp only [PDefs.fills, decide_true, Bool.and_self]
  | _, .trm _ none t, _, _, h => by
      simp only [PDefs.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PDefs.fills, decide_true, Bool.true_and, PTm.fills_of_full? ht]
  | _, .trm _ (some _) _, _, _, h => by simp only [PDefs.full?, reduceCtorEq] at h
  | _, .and d1 d2, _, T, h => by
      simp only [PDefs.full?] at h
      cases h1 : d1.full? with
      | none => simp only [h1, reduceCtorEq] at h
      | some b =>
          cases h2 : d2.full? with
          | none => simp only [h1, h2, reduceCtorEq] at h
          | some c =>
              simp only [h1, h2, Option.some.injEq] at h
              subst h
              simp only [PDefs.fills, PDefs.fills_of_full? (andLeft T) h1,
                PDefs.fills_of_full? (andRight T) h2, Bool.and_self]
end

mutual
/-- `toI` keeps the node count. -/
theorem sizePTm_toI : ∀ {s : Sig} (a : ATm s), sizePTm a.toI = sizeATm a
  | _, .path _ => rfl
  | _, .lam _ t => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t]
  | _, .obj _ d => by simp only [ATm.toI, sizePTm, sizeATm, sizePDefs_toI d]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let _ t u => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t, sizePTm_toI u]
/-- `toI` keeps the node count of definitions. -/
theorem sizePDefs_toI : ∀ {s : Sig} (d : ADefs s), sizePDefs d.toI = sizeADefs d
  | _, .typ _ _ => rfl
  | _, .trm _ t => by simp only [ADefs.toI, sizePDefs, sizeADefs, sizePTm_toI t]
  | _, .and d e => by
      simp only [ADefs.toI, sizePDefs, sizeADefs, sizePDefs_toI d, sizePDefs_toI e]
end

end PathsFrontend
