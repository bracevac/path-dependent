import Coercions.ScalaSyntax.Ast

/-!
# The syntax tree of the pDOT Scala subset

The tree that the pDOT reader builds from the tokens of a `.scala` file (plan
XI, D-5, "XS: the Scala subset").  It is a tree of its own, beside the vanilla
`ScalaSyntax.Program`: pDOT has paths of any length, objects as members,
`def`s with one parameter per list, and type members of objects that are
aliases.

Every node that a check can refuse carries its `Pos`, as in the vanilla tree.
A node that names something sits at the name.  Any other node sits at the
token that makes it: `Any`, `this`, the `{` of a refinement or a block, the
`new` of a literal, the arrow of a function type, the `:` of an ascription.

A term path is `Tm.path`: the parser folds every selection on a path into a
longer path, so later stages see each path whole.  A bound is the inductive
`Bound` of the same mutual block, so the tree derives `DecidableEq` with no
well-founded recursion.

Lists of recursive nodes are spines (`Decls`, `Stats`, `Mems`), so every walk
is structural.  `File.erase` sets every position to `⟨0, 0⟩`, so tests and
round trips compare trees up to positions.  `Path.text`, `Path.pos`,
`Path.root`, `Path.isRoot` and `Path.firstStep?` serve the later checks.

This module imports the vanilla tree, for `ScalaSyntax.Pos.zero`, and opens
only `Pos`, so the vanilla `Path` and `Ty` stay out of scope.
-/

namespace NominalFrontend.ScalaRead

open ScalaSyntax (Pos)

/-! ## Paths and types -/

/-- A path: a root, then field selections. -/
inductive Path where
  /-- `this`, the innermost refinement, object or literal, or the stem. -/
  | this (p : Pos)
  /-- `x`, a variable or a member, by name. -/
  | var (p : Pos) (x : String)
  /-- `q.a`, at `a`. -/
  | sel (q : Path) (p : Pos) (a : String)
deriving DecidableEq, Repr

mutual
/-- A written type. -/
inductive Ty where
  /-- `Any`. -/
  | any (p : Pos)
  /-- `Nothing`. -/
  | nothing (p : Pos)
  /-- `q.A`, at `A`. -/
  | sel (p : Pos) (q : Path) (A : String)
  /-- `q.type`, at `type`. -/
  | sngl (p : Pos) (q : Path)
  /-- `A`, a bare type member (D-11). -/
  | name (p : Pos) (A : String)
  /-- `{ d1; …; dn }`, at `{`. -/
  | refine (p : Pos) (ds : Decls)
  /-- `S & T`, nested to the left. -/
  | and (S T : Ty)
  /-- `(x: S) => T` or `S => T`, at `=>`. -/
  | fn (p : Pos) (x : Option String) (S T : Ty)
/-- A bound of an abstract type member. -/
inductive Bound where
  /-- No bound written. -/
  | absent
  /-- `>: T` or `<: T`. -/
  | given (T : Ty)
/-- The declarations of a refinement. -/
inductive Decls where
  /-- No more declarations. -/
  | nil
  /-- `type A >: lo <: hi`, at `A`. -/
  | typ (p : Pos) (A : String) (lo hi : Bound) (rest : Decls)
  /-- `type A = T`, at `A`. -/
  | alias (p : Pos) (A : String) (T : Ty) (rest : Decls)
  /-- `val a: T`, at `a`. -/
  | val (p : Pos) (a : String) (T : Ty) (rest : Decls)
end
deriving instance DecidableEq, Repr for Ty, Bound, Decls

/-- A parameter of a `def`, `(x: T)`. -/
structure Param where
  /-- At the name. -/
  pos : Pos
  name : String
  ty : Ty
deriving DecidableEq, Repr

/-! ## Terms and members -/

mutual
/-- A term. -/
inductive Tm where
  /-- `x`, `this`, `q.a`: a path. -/
  | path (q : Path)
  /-- `t.a`, at `a`.  `t` is never a `path`: the parser folds a selection on a
  path into the path. -/
  | sel (t : Tm) (p : Pos) (a : String)
  /-- `t(u)`. -/
  | app (t u : Tm)
  /-- `(x: T) => e`, `x => e` or `(x) => e`, at `x`. -/
  | lam (p : Pos) (x : String) (T : Option Ty) (body : Tm)
  /-- `(t: T)`, at `:`. -/
  | asc (p : Pos) (t : Tm) (T : Ty)
  /-- `{ val …; e }`, at `{`. -/
  | block (p : Pos) (ss : Stats)
  /-- `new Object { s => ms }`, at `new`. -/
  | lit (p : Pos) (self : Option String) (ms : Mems)
/-- The statements of a block. -/
inductive Stats where
  /-- The result, `e`. -/
  | last (t : Tm)
  /-- `val x [: T] = rhs`, at `x`. -/
  | val (p : Pos) (x : String) (T : Option Ty) (rhs : Tm) (rest : Stats)
/-- The members of the wrapper, an object or a literal. -/
inductive Mems where
  /-- No more members. -/
  | nil
  /-- `object o { s => body }`, at `o`. -/
  | obj (p : Pos) (o : String) (self : Option String) (body : Mems) (rest : Mems)
  /-- `type A = T`, at `A`. -/
  | typ (p : Pos) (A : String) (T : Ty) (rest : Mems)
  /-- `val a [: T] = rhs`, at `a`. -/
  | val (p : Pos) (a : String) (T : Option Ty) (rhs : Tm) (rest : Mems)
  /-- `def f(x1: S1)…(xn: Sn) [: R] = body`, at `f`. -/
  | defn (p : Pos) (f : String) (ps : List Param) (R : Option Ty) (body : Tm) (rest : Mems)
end
deriving instance DecidableEq, Repr for Tm, Stats, Mems

/-- A file: the wrapper object, its members, and `val program [: T] = body`. -/
structure File where
  /-- At the wrapper's name. -/
  pos : Pos
  /-- The wrapper object. -/
  name : String
  /-- Its members, before `program`. -/
  mems : Mems
  /-- The written type of `program`. -/
  ty : Option Ty
  /-- The right side of `program`. -/
  body : Tm
deriving DecidableEq, Repr

/-! ## Positions erased -/

/-- A path without positions. -/
def Path.erase : Path → Path
  | .this _ => .this ScalaSyntax.Pos.zero
  | .var _ x => .var ScalaSyntax.Pos.zero x
  | .sel q _ a => .sel q.erase ScalaSyntax.Pos.zero a

mutual
/-- A type without positions. -/
def Ty.erase (T : Ty) : Ty :=
  match T with
  | .any _ => .any ScalaSyntax.Pos.zero
  | .nothing _ => .nothing ScalaSyntax.Pos.zero
  | .sel _ q A => .sel ScalaSyntax.Pos.zero q.erase A
  | .sngl _ q => .sngl ScalaSyntax.Pos.zero q.erase
  | .name _ A => .name ScalaSyntax.Pos.zero A
  | .refine _ ds => .refine ScalaSyntax.Pos.zero (Decls.erase ds)
  | .and S U => .and (Ty.erase S) (Ty.erase U)
  | .fn _ x S U => .fn ScalaSyntax.Pos.zero x (Ty.erase S) (Ty.erase U)
termination_by structural T
/-- A bound without positions. -/
def Bound.erase (b : Bound) : Bound :=
  match b with
  | .absent => .absent
  | .given T => .given (Ty.erase T)
termination_by structural b
/-- Declarations without positions. -/
def Decls.erase (ds : Decls) : Decls :=
  match ds with
  | .nil => .nil
  | .typ _ A lo hi r => .typ ScalaSyntax.Pos.zero A (Bound.erase lo) (Bound.erase hi) (Decls.erase r)
  | .alias _ A T r => .alias ScalaSyntax.Pos.zero A (Ty.erase T) (Decls.erase r)
  | .val _ a T r => .val ScalaSyntax.Pos.zero a (Ty.erase T) (Decls.erase r)
termination_by structural ds
end

/-- A parameter without positions. -/
def Param.erase (x : Param) : Param := ⟨ScalaSyntax.Pos.zero, x.name, x.ty.erase⟩

mutual
/-- A term without positions. -/
def Tm.erase (t : Tm) : Tm :=
  match t with
  | .path q => .path q.erase
  | .sel u _ a => .sel (Tm.erase u) ScalaSyntax.Pos.zero a
  | .app u v => .app (Tm.erase u) (Tm.erase v)
  | .lam _ x T b => .lam ScalaSyntax.Pos.zero x (T.map Ty.erase) (Tm.erase b)
  | .asc _ u T => .asc ScalaSyntax.Pos.zero (Tm.erase u) T.erase
  | .block _ ss => .block ScalaSyntax.Pos.zero (Stats.erase ss)
  | .lit _ s ms => .lit ScalaSyntax.Pos.zero s (Mems.erase ms)
termination_by structural t
/-- Statements without positions. -/
def Stats.erase (ss : Stats) : Stats :=
  match ss with
  | .last t => .last (Tm.erase t)
  | .val _ x T e r => .val ScalaSyntax.Pos.zero x (T.map Ty.erase) (Tm.erase e) (Stats.erase r)
termination_by structural ss
/-- Members without positions. -/
def Mems.erase (ms : Mems) : Mems :=
  match ms with
  | .nil => .nil
  | .obj _ o s b r => .obj ScalaSyntax.Pos.zero o s (Mems.erase b) (Mems.erase r)
  | .typ _ A T r => .typ ScalaSyntax.Pos.zero A T.erase (Mems.erase r)
  | .val _ a T e r => .val ScalaSyntax.Pos.zero a (T.map Ty.erase) (Tm.erase e) (Mems.erase r)
  | .defn _ f ps R e r =>
    .defn ScalaSyntax.Pos.zero f (ps.map Param.erase) (R.map Ty.erase) (Tm.erase e) (Mems.erase r)
termination_by structural ms
end

/-- A file without positions. -/
def File.erase (F : File) : File :=
  ⟨ScalaSyntax.Pos.zero, F.name, F.mems.erase, F.ty.map Ty.erase, F.body.erase⟩

/-! ## Paths, for the checks -/

/-- A path as text, for messages: `this`, `x`, `q.a`. -/
def Path.text : Path → String
  | .this _ => "this"
  | .var _ x => x
  | .sel q _ a => q.text ++ "." ++ a

/-- The position of the last step, or of the root. -/
def Path.pos : Path → Pos
  | .this p | .var p _ | .sel _ p _ => p

/-- The root of a path, `this` or a variable. -/
def Path.root : Path → Path
  | .sel q _ _ => q.root
  | q => q

/-- Whether a path has no step. -/
def Path.isRoot : Path → Bool
  | .this _ | .var _ _ => true
  | .sel .. => false

/-- The position of the first field step of a path, if any. -/
def Path.firstStep? : Path → Option Pos
  | .this _ | .var _ _ => none
  | .sel q p _ => match q.firstStep? with
    | some r => some r
    | none => some p

end NominalFrontend.ScalaRead
