import LambdaPFC.Evidence

/-!
A small runtime model for the first evidence-passing experiment.

Types are interpreted under a valuation of their intrinsically scoped free
variables.  Extending a valuation with the first component of a pair gives a
direct semantic account of the dependent member binder; no syntactic opening
lemma is needed in the pair case.
-/

namespace LambdaPFC

open LambdaP

/-- A valuation sends scoped variables to runtime locations. -/
abbrev Valuation (n m : Nat) := Fin n -> Fin m

namespace Valuation

/-- Extend a valuation with the location supplied for the newest binder. -/
def snoc (rho : Valuation n m) (x : Fin m) : Valuation (n + 1) m :=
  Fin.cases x rho

/-- Precompose a valuation with a scoped renaming. -/
def comp (rho : Valuation k m) (f : FinFun n k) : Valuation n m :=
  fun i => rho (f i)

/-- Extending a composed valuation agrees with composing extended maps. -/
@[simp] theorem comp_ext_snoc
    (rho : Valuation k m) (f : FinFun n k) (y : Fin m) :
    (rho.comp f).snoc y = (rho.snoc y).comp f.ext := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Weakening ignores the newest entry of an extended valuation. -/
@[simp] theorem comp_weaken_snoc
    (rho : Valuation n m) (y : Fin m) :
    (rho.snoc y).comp FinFun.weaken = rho := by
  funext i
  rfl

end Valuation

/-- Runtime endpoints are either locations or stored type witnesses. -/
inductive Endpoint (m : Nat) where
| val : Fin m -> Endpoint m
| type : Ty m -> Endpoint m

/-- The runtime cells needed by the pair experiment. -/
inductive Cell (m : Nat) where
| atom : Cell m
| pair : Fin m -> Name -> Endpoint m -> Cell m

/-- A finite runtime store. -/
abbrev Model (m : Nat) := Fin m -> Cell m

/-- Lookup of a named member, following the first-component spine on misses. -/
inductive Select (M : Model m) : Fin m -> Name -> Endpoint m -> Prop where
| hit :
    M x = .pair y a e ->
    Select M x a e
| miss :
    M x = .pair y b e ->
    Not (a = b) ->
    Select M y a r ->
    Select M x a r

/-- Big-step resolution of a scoped path under a runtime valuation. -/
inductive Resolve (M : Model m) (rho : Valuation n m) :
    Path n -> Endpoint m -> Prop where
| var : Resolve M rho (.var x) (.val (rho x))
| fst :
    Resolve M rho p (.val x) ->
    M x = .pair y a e ->
    Resolve M rho p.fst (.val y)
| sel :
    Resolve M rho p (.val x) ->
    Select M x a e ->
    Resolve M rho (p.sel a) e

/-- Member lookup is deterministic. -/
theorem Select.deterministic
    (h1 : Select M x a e1) (h2 : Select M x a e2) : e1 = e2 := by
  induction h1 generalizing e2 with
  | hit hcell1 =>
      cases h2 with
      | hit hcell2 =>
          cases hcell1.symm.trans hcell2
          rfl
      | miss hcell2 hne _ =>
          cases hcell1.symm.trans hcell2
          exact (hne rfl).elim
  | miss hcell1 hne1 hselect1 ih =>
      cases h2 with
      | hit hcell2 =>
          cases hcell1.symm.trans hcell2
          exact (hne1 rfl).elim
      | miss hcell2 _ hselect2 =>
          cases hcell1.symm.trans hcell2
          exact ih hselect2

/-- Path resolution is deterministic. -/
theorem Resolve.deterministic
    (h1 : Resolve M rho p e1) (h2 : Resolve M rho p e2) : e1 = e2 := by
  induction h1 generalizing e2 with
  | var =>
      cases h2
      rfl
  | fst hpath1 hcell1 ih =>
      cases h2 with
      | fst hpath2 hcell2 =>
          cases ih hpath2
          cases hcell1.symm.trans hcell2
          rfl
  | sel hpath1 hselect1 ih =>
      cases h2 with
      | sel hpath2 hselect2 =>
          cases ih hpath2
          exact hselect1.deterministic hselect2

/-- Path resolution is natural with respect to renaming. -/
theorem Resolve.rename
    (h : Resolve M (rho.comp f) p e) :
    Resolve M rho (p.rename f) e := by
  induction h with
  | var => exact .var
  | fst _ hcell ih => exact .fst ih hcell
  | sel _ hselect ih => exact .sel ih hselect

/--
Positive realization for the proper-member pair fragment.  The pair clause
interprets the member under the valuation extended with the actual first
location.  `Top`, singleton types, and dependent pairs are the inhabited forms
needed by the initial probe; `Bot` has no constructor.
-/
inductive Possible (M : Model m) :
    {n : Nat} -> Valuation n m -> Fin m -> Ty n -> Prop where
| top : Possible M rho x .Top
| single :
    Resolve M rho p (.val x) ->
    Possible M rho x (.Single p)
| pair :
    M x = .pair y a (.val z) ->
    Possible M rho y S ->
    Possible M (rho.snoc y) z T ->
    Possible M rho x (.Pair S a (.ty T))

/-- General semantic renaming, stated with an explicit valuation equation. -/
theorem Possible.renameAux
    {n m : Nat} {M : Model m} {sigma : Valuation n m}
    {x : Fin m} {T : Ty n}
    (h : Possible M sigma x T) :
    forall {k} (f : FinFun n k) (rho : Valuation k m),
      sigma = rho.comp f ->
      Possible M rho x (T.rename f) := by
  induction h with
  | top =>
      intro k f rho hsigma
      exact .top
  | single hp =>
      intro k f rho hsigma
      cases hsigma
      exact .single hp.rename
  | pair hcell hFirst hMember ihFirst ihMember =>
      intro k f rho hsigma
      apply Possible.pair hcell
      · exact ihFirst f rho hsigma
      · apply ihMember f.ext (rho.snoc _)
        rw [hsigma]
        exact Valuation.comp_ext_snoc rho f _

/-- Positive realization is natural with respect to renaming. -/
theorem Possible.rename
    {n k m : Nat} {M : Model m} {rho : Valuation k m}
    {f : FinFun n k} {x : Fin m} {T : Ty n}
    (h : Possible M (rho.comp f) x T) :
    Possible M rho x (T.rename f) :=
  h.renameAux f rho rfl

/-- Semantic action denoted by an evidence sort. -/
def EvSort.Action {n m : Nat}
    (s : EvSort n) (M : Model m) (rho : Valuation n m) : Prop :=
  match s with
  | .map S T =>
      forall x, Possible M rho x S -> Possible M rho x T
  | .abs S T U =>
      forall y, Possible M rho y S ->
        forall z, Possible M (rho.snoc y) z T ->
          Possible M (rho.snoc y) z U

/-- Every evidence term acts on realizations of its source. -/
theorem Evidence.action {n : Nat} {s : EvSort n} (c : Evidence s) :
    forall {m} (M : Model m) (rho : Valuation n m), s.Action M rho := by
  induction c with
  | refl =>
      intro m M rho x hx
      exact hx
  | trans _ _ ih1 ih2 =>
      intro m M rho x hx
      exact ih2 M rho x (ih1 M rho x hx)
  | bot =>
      intro m M rho x hx
      cases hx
  | top =>
      intro m M rho x hx
      exact .top
  | lam _ ih =>
      intro m M rho y hy z hz
      exact ih M (rho.snoc y) z hz
  | bound =>
      intro m M rho y hy z hz
      cases hz with
      | single hresolve =>
          have hzero :
              Resolve M (rho.snoc y) (.var 0) (.val y) := by
            exact .var
          have he := hresolve.deterministic hzero
          cases he
          exact hy.renameAux FinFun.weaken (rho.snoc y)
            (Valuation.comp_weaken_snoc rho y).symm
  | absTrans _ _ ih1 ih2 =>
      intro m M rho y hy z hz
      exact ih2 M rho y hy z (ih1 M rho y hy z hz)
  | pair _ _ ihFirst ihMember =>
      intro m M rho x hx
      cases hx with
      | pair hcell hFirst hMember =>
          exact .pair hcell
            (ihFirst M rho _ hFirst)
            (ihMember M rho _ hFirst _ hMember)

/-- A runtime location paired with its realization proof. -/
structure Typed {m n : Nat}
    (M : Model m) (rho : Valuation n m) (T : Ty n) where
  raw : Fin m
  realizes : Possible M rho raw T

/-- Apply evidence to a typed location.  Runtime data is left unchanged. -/
def Evidence.cast {n m : Nat} {S T : Ty n}
    (c : Evidence (.map S T)) {M : Model m} {rho : Valuation n m}
    (v : Typed M rho S) : Typed M rho T :=
  ⟨v.raw, c.action M rho v.raw v.realizes⟩

/-- Erasure observes only the underlying runtime location. -/
def Typed.erase {n m : Nat} {M : Model m} {rho : Valuation n m} {T : Ty n}
    (v : Typed M rho T) : Fin m := v.raw

@[simp] theorem Evidence.erase_cast {n m : Nat} {S T : Ty n}
    {M : Model m} {rho : Valuation n m}
    (c : Evidence (.map S T)) (v : Typed M rho S) :
    (c.cast v).erase = v.erase := rfl

/-- The first projection observable in the runtime model. -/
def Typed.first? {n m : Nat} {M : Model m} {rho : Valuation n m} {T : Ty n}
    (v : Typed M rho T) : Option (Fin m) :=
  match M v.raw with
  | .atom => none
  | .pair y _ _ => some y

/-- The member observable in the runtime model. -/
def Typed.member? {n m : Nat} {M : Model m} {rho : Valuation n m} {T : Ty n}
    (v : Typed M rho T) : Option (Endpoint m) :=
  match M v.raw with
  | .atom => none
  | .pair _ _ e => some e

@[simp] theorem Evidence.first_cast {n m : Nat} {S T : Ty n}
    {M : Model m} {rho : Valuation n m}
    (c : Evidence (.map S T)) (v : Typed M rho S) :
    (c.cast v).first? = v.first? := rfl

@[simp] theorem Evidence.member_cast {n m : Nat} {S T : Ty n}
    {M : Model m} {rho : Valuation n m}
    (c : Evidence (.map S T)) (v : Typed M rho S) :
    (c.cast v).member? = v.member? := rfl

/-- The unrestricted pair rule acts by delaying the member map to run time. -/
theorem Evidence.unrestricted_pair_action
    {n m : Nat} {S S' : Ty n} {T T' : Ty (n + 1)} {a : Name}
    (cFirst : Evidence (.map S S'))
    (cMember : Evidence (.abs S T T'))
    (M : Model m) (rho : Valuation n m) :
    forall x,
      Possible M rho x (.Pair S a (.ty T)) ->
      Possible M rho x (.Pair S' a (.ty T')) :=
  (Evidence.pair cFirst cMember).action M rho

end LambdaPFC
