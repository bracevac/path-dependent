import Coercions.DOT.TraceablePaths.Source.Runtime

/-!
# Traceable-path regressions

The positive example resolves `r.a.b` through two transparent alias records.
The negative examples show that a missing field, a fresh binder, and a dynamic
receiver cannot acquire a trace certificate.
-/

namespace DotFCRP.Source.NestedExample

open DotFC

def a : Name := 10
def b : Name := 11
def typeLabel : Name := 12
def missing : Name := 99

/-- Three ambient variables, newest last: `r`, `s`, and final anchor `t`. -/
abbrev Scope : Sig := (([] ▹ .term) ▹ .term) ▹ .term

def t : BVar Scope .term := .here
def s : BVar Scope .term := .there .here
def r : BVar Scope .term := .there (.there .here)

def rPath : Path Scope := .var r
def sPath : Path Scope := .var s
def tPath : Path Scope := .var t
def ra : Path Scope := .select rPath a
def rab : Path Scope := .select ra b

def rField : AliasField Scope :=
  ⟨r, a, sPath⟩

def sField : AliasField Scope :=
  ⟨s, b, tPath⟩

/-- Newest-first transparent record spine. -/
def store : AliasStore Scope := [sField, rField]

def rLookup : FieldAt store r a sPath :=
  .there (Or.inl (by decide)) .here

def sLookup : FieldAt store s b tPath :=
  .here

def rTrace : Traceable store rPath r := .var

def raTrace : Traceable store ra s :=
  .select rTrace rLookup .var

/-- The accepted nested path `r.a.b` resolves deterministically to `t`. -/
def rabTrace : Traceable store rab t :=
  .select raTrace sLookup .var

def rabEqualsT : PathEq store rab tPath :=
  ⟨t, rabTrace, .var⟩

def rabReducesToT : PathStep store rab tPath :=
  .field raTrace sLookup (.var)

def runtimeReduction :
    Runtime.Step store (Runtime.Tm.ofPath rab) (Runtime.Tm.ofPath tPath) :=
  Runtime.Step.ofPathStep rabReducesToT

/-- The alternative compatible-rewrite branch reduces the inner `r.a`
selection first. -/
def raReducesToS : PathStep store ra sPath :=
  .field rTrace rLookup (.var)

def sb : Path Scope := .select sPath b

def sbReducesToT : PathStep store sb tPath :=
  .field (.var) sLookup (.var)

def receiverFirstReduction : Runtime.Step store
    (Runtime.Tm.ofPath rab) (Runtime.Tm.ofPath sb) := by
  exact .selectReceiver (Runtime.Step.ofPathStep raReducesToS)

def receiverFirstJoinsAtT : Runtime.Step store
    (Runtime.Tm.ofPath sb) (Runtime.Tm.ofPath tPath) :=
  Runtime.Step.ofPathStep sbReducesToT

/-- Direct collapse and receiver-first rewriting join at the same anchor. -/
theorem nested_rewrite_joinable :
    Runtime.Step store (Runtime.Tm.ofPath rab) (Runtime.Tm.ofPath tPath) ∧
      ∃ middle,
        Runtime.Step store (Runtime.Tm.ofPath rab) middle ∧
        Runtime.Step store middle (Runtime.Tm.ofPath tPath) :=
  ⟨runtimeReduction, ⟨Runtime.Tm.ofPath sb,
    receiverFirstReduction, receiverFirstJoinsAtT⟩⟩

theorem rab_anchor_unique {anchor : BVar Scope .term}
    (trace : Traceable store rab anchor) : anchor = t :=
  Traceable.deterministic trace rabTrace

/-! ## Native singleton and path-selection formation -/

def context : Ctx Scope :=
  ((Ctx.nil.snoc (.top : Ty []))
    |>.snoc (.top : Ty ([] ▹ .term)))
    |>.snoc (.member typeLabel .top .top)

def tLookupType :
    Lookup context t (.member typeLabel .top .top) :=
  .here

def rabBinding :
    PathBinding store context rab (.member typeLabel .top .top) :=
  ⟨t, rabTrace, tLookupType⟩

def singletonWf : Wf store context (.singleton rab) :=
  .singleton rabBinding

def selectionHandle : Handle store context rab typeLabel .top .top :=
  .direct rabBinding .here

/-- Types may select a member through the nested path `r.a.b.A`. -/
def selectionWf : Wf store context (.sel rab typeLabel) :=
  .sel selectionHandle

/-- Co-resolution transports the nested path term to the anchor's type. -/
def nestedTermTyping :
    HasTy store context (.ref rab) (.member typeLabel .top .top) :=
  .path rabBinding

/-! ## Rejected boundaries -/

def unresolved : Path Scope := .select rPath missing

/-- No record in the finite spine defines `r.missing`. -/
theorem unresolved_not_traceable (anchor : BVar Scope .term) :
    Traceable store unresolved anchor → False := by
  intro trace
  cases trace with
  | select _ field _ =>
      cases field with
      | there _ older =>
          cases older with
          | there _ absent => cases absent

/-- Weakening an ambient variable does not alias the new binder. -/
theorem fresh_binder_separate :
    CoResolved (store.weaken (kind := .term)) rPath.weaken (.var .here) →
      False :=
  weakened_not_coResolved_fresh rTrace

/-- The fresh binder nevertheless retains its own reflexive identity. -/
def fresh_binder_refl :
    CoResolved (store.weaken (kind := .term)) (.var .here) (.var .here) :=
  freshRefl

/-- A dynamic receiver is outside the certified traceable fragment. -/
theorem dynamic_receiver_rejected :
    Runtime.TraceableReceiver store
      (.dynamic (Runtime.Tm.app (.var r) (.var s))) → False :=
  Runtime.dynamic_not_traceable store _

end DotFCRP.Source.NestedExample
