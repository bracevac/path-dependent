From PathDependent.LambdaPCC Require Import FinFun Syntax Context.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Precise path typing.  The kind distinguishes term, type, and
    capture-set members. *)
Inductive PathTy {n : nat} (Gamma : Ctx n) :
    forall k : Kind, Path n -> Tau n k -> Type :=
| PT_var (x : Fin n) :
    PathTy Gamma (PVar x) (TauTerm (ctx_lookup Gamma x))
| PT_fst {k : Kind} (p : Path n) (C : CaptureSet n)
    (S0 : Ty n) (a : Name) (d : Tau (S n) k) :
    PathTy Gamma p (TauTerm (TyCapt C (ShPair S0 a d))) ->
    PathTy Gamma (PFst p) (TauTerm S0)
| PT_sel_r {k : Kind} (p : Path n) (C : CaptureSet n)
    (S0 : Ty n) (a : Name) (d : Tau (S n) k) :
    PathTy Gamma p (TauTerm (TyCapt C (ShPair S0 a d))) ->
    PathTy Gamma (PSel p a) (tau_open d (PFst p))
| PT_sel_l {receiver_kind member_kind : Kind}
    (p : Path n) (C : CaptureSet n) (S0 : Ty n)
    (b : Name) (stored : Tau (S n) receiver_kind)
    (a : Name) (d : Tau n member_kind) :
    PathTy Gamma p (TauTerm (TyCapt C (ShPair S0 b stored))) ->
    PathTy Gamma (PSel (PFst p) a) d ->
    a <> b ->
    PathTy Gamma (PSel p a) d.

Arguments PathTy {n} Gamma {k} _ _.

(** Subcapturing. *)
Inductive CaptureSub {n : nat} (Gamma : Ctx n) :
    CaptureSet n -> CaptureSet n -> Type :=
| CS_refl (C : CaptureSet n) : CaptureSub Gamma C C
| CS_trans (C D E : CaptureSet n) :
    CaptureSub Gamma C D -> CaptureSub Gamma D E -> CaptureSub Gamma C E
| CS_empty (C : CaptureSet n) : CaptureSub Gamma CEmpty C
| CS_union_left (C D : CaptureSet n) :
    CaptureSub Gamma C (CUnion C D)
| CS_union_right (C D : CaptureSet n) :
    CaptureSub Gamma D (CUnion C D)
| CS_union_elim (C D E : CaptureSet n) :
    CaptureSub Gamma C E -> CaptureSub Gamma D E ->
    CaptureSub Gamma (CUnion C D) E
| CS_path (p : Path n) (C : CaptureSet n) (shape : Shape n) :
    PathTy Gamma p (TauTerm (TyCapt C shape)) ->
    CaptureSub Gamma (CSingleton p) C
| CS_alias (p q : Path n) (C : CaptureSet n) :
    PathTy Gamma p (TauTerm (TyCapt C (ShSingle q))) ->
    CaptureSub Gamma (CSingleton q) (CSingleton p)
| CS_fst_root (p : Path n) (T : Ty n) :
    PathTy Gamma (PFst p) (TauTerm T) ->
    CaptureSub Gamma (CSingleton (PFst p)) (CSingleton p)
| CS_sel_root (p : Path n) (a : Name) (T : Ty n) :
    PathTy Gamma (PSel p a) (TauTerm T) ->
    CaptureSub Gamma (CSingleton (PSel p a)) (CSingleton p)
| CS_select_lower (p : Path n) (a : Name)
    (L U : CaptureSet n) :
    PathTy Gamma (PSel p a) (TauCapture L U) ->
    CaptureSub Gamma L U ->
    CaptureSub Gamma L (CSelect p a)
| CS_select_upper (p : Path n) (a : Name)
    (L U : CaptureSet n) :
    PathTy Gamma (PSel p a) (TauCapture L U) ->
    CaptureSub Gamma L U ->
    CaptureSub Gamma (CSelect p a) U.

(** Capturing-type, shape, and member-signature subtyping. *)
Inductive TySub {n : nat} (Gamma : Ctx n) : Ty n -> Ty n -> Type :=
| TS_refl (T : Ty n) : TySub Gamma T T
| TS_trans (S0 T U : Ty n) :
    TySub Gamma S0 T -> TySub Gamma T U -> TySub Gamma S0 U
| TS_capt (C D : CaptureSet n) (S0 T : Shape n) :
    CaptureSub Gamma C D -> ShapeSub Gamma S0 T ->
    TySub Gamma (TyCapt C S0) (TyCapt D T)
with ShapeSub {n : nat} (Gamma : Ctx n) :
    Shape n -> Shape n -> Type :=
| SS_refl (S0 : Shape n) : ShapeSub Gamma S0 S0
| SS_trans (S0 T U : Shape n) :
    ShapeSub Gamma S0 T -> ShapeSub Gamma T U -> ShapeSub Gamma S0 U
| SS_bot (S0 : Shape n) : ShapeSub Gamma ShBot S0
| SS_top (S0 : Shape n) : ShapeSub Gamma S0 ShTop
| SS_singleton_widen (p : Path n) (C : CaptureSet n) (S0 : Shape n) :
    PathTy Gamma p (TauTerm (TyCapt C S0)) ->
    ShapeSub Gamma (ShSingle p) S0
| SS_singleton_alias (p q : Path n) (C : CaptureSet n) :
    PathTy Gamma p (TauTerm (TyCapt C (ShSingle q))) ->
    ShapeSub Gamma (ShSingle q) (ShSingle p)
| SS_select_lower (p : Path n) (a : Name) (S0 T : Shape n) :
    PathTy Gamma (PSel p a) (TauType S0 T) ->
    ShapeSub Gamma S0 T -> ShapeSub Gamma S0 (ShTSel p a)
| SS_select_upper (p : Path n) (a : Name) (S0 T : Shape n) :
    PathTy Gamma (PSel p a) (TauType S0 T) ->
    ShapeSub Gamma S0 T -> ShapeSub Gamma (ShTSel p a) T
| SS_fun (S0 Sprime : Ty n) (T Tprime : Ty (S n)) :
    TySub Gamma Sprime S0 ->
    TySub (CtxSnoc Gamma Sprime) T Tprime ->
    ShapeSub Gamma (ShFun S0 T) (ShFun Sprime Tprime)
| SS_pair {k : Kind} (S0 Sprime : Ty n) (a : Name)
    (d dprime : Tau (S n) k) :
    TySub Gamma S0 Sprime ->
    TauSub (CtxSnoc Gamma S0) d dprime ->
    ShapeSub Gamma (ShPair S0 a d) (ShPair Sprime a dprime)
with TauSub {n : nat} (Gamma : Ctx n) :
    forall k : Kind, Tau n k -> Tau n k -> Type :=
| TAS_refl (k : Kind) (d : Tau n k) : TauSub Gamma d d
| TAS_trans (k : Kind) (d e f : Tau n k) :
    TauSub Gamma d e -> TauSub Gamma e f -> TauSub Gamma d f
| TAS_term (S0 T : Ty n) :
    TySub Gamma S0 T -> TauSub Gamma (TauTerm S0) (TauTerm T)
| TAS_type (S0 T Sprime Tprime : Shape n) :
    ShapeSub Gamma Sprime S0 -> ShapeSub Gamma T Tprime ->
    ShapeSub Gamma S0 T ->
    TauSub Gamma (TauType S0 T) (TauType Sprime Tprime)
| TAS_capture (L U Lprime Uprime : CaptureSet n) :
    CaptureSub Gamma Lprime L -> CaptureSub Gamma U Uprime ->
    CaptureSub Gamma L U ->
    TauSub Gamma (TauCapture L U) (TauCapture Lprime Uprime).

Arguments TySub {n} Gamma _ _.
Arguments ShapeSub {n} Gamma _ _.
Arguments TauSub {n} Gamma {k} _ _.

(** Well-formedness. *)
Inductive CaptureWf {n : nat} (Gamma : Ctx n) : CaptureSet n -> Type :=
| CW_empty : CaptureWf Gamma CEmpty
| CW_union (C D : CaptureSet n) :
    CaptureWf Gamma C -> CaptureWf Gamma D -> CaptureWf Gamma (CUnion C D)
| CW_singleton (p : Path n) (T : Ty n) :
    PathTy Gamma p (TauTerm T) -> CaptureWf Gamma (CSingleton p)
| CW_select (p : Path n) (a : Name) (L U : CaptureSet n) :
    PathTy Gamma (PSel p a) (TauCapture L U) ->
    CaptureSub Gamma L U -> CaptureWf Gamma (CSelect p a).

Inductive TyWf {n : nat} (Gamma : Ctx n) : Ty n -> Type :=
| TW_capt (C : CaptureSet n) (shape : Shape n) :
    CaptureWf Gamma C -> ShapeWf Gamma shape ->
    TyWf Gamma (TyCapt C shape)
with ShapeWf {n : nat} (Gamma : Ctx n) : Shape n -> Type :=
| SW_bot : ShapeWf Gamma ShBot
| SW_top : ShapeWf Gamma ShTop
| SW_singleton (p : Path n) (T : Ty n) :
    PathTy Gamma p (TauTerm T) -> ShapeWf Gamma (ShSingle p)
| SW_select (p : Path n) (a : Name) (S0 T : Shape n) :
    PathTy Gamma (PSel p a) (TauType S0 T) ->
    ShapeSub Gamma S0 T -> ShapeWf Gamma (ShTSel p a)
| SW_fun (S0 : Ty n) (T : Ty (S n)) :
    TyWf Gamma S0 -> TyWf (CtxSnoc Gamma S0) T ->
    ShapeWf Gamma (ShFun S0 T)
| SW_pair {k : Kind} (S0 : Ty n) (a : Name) (d : Tau (S n) k) :
    TyWf Gamma S0 -> TauWf (CtxSnoc Gamma S0) d ->
    ShapeWf Gamma (ShPair S0 a d)
with TauWf {n : nat} (Gamma : Ctx n) :
    forall k : Kind, Tau n k -> Type :=
| TAW_term (T : Ty n) : TyWf Gamma T -> TauWf Gamma (TauTerm T)
| TAW_type (S0 T : Shape n) :
    ShapeWf Gamma S0 -> ShapeWf Gamma T -> ShapeSub Gamma S0 T ->
    TauWf Gamma (TauType S0 T)
| TAW_capture (L U : CaptureSet n) :
    CaptureWf Gamma L -> CaptureWf Gamma U -> CaptureSub Gamma L U ->
    TauWf Gamma (TauCapture L U).

Arguments TyWf {n} Gamma _.
Arguments ShapeWf {n} Gamma _.
Arguments TauWf {n} Gamma {k} _.

(** Term typing jointly records result type and evaluation-use set. *)
Inductive TermTy {n : nat} (Gamma : Ctx n) :
    Tm n -> Ty n -> CaptureSet n -> Type :=
| TT_path (p : Path n) (T : Ty n) :
    PathTy Gamma p (TauTerm T) ->
    TermTy Gamma (TmPath p)
      (TyCapt (CSingleton p) (ShSingle p)) (CSingleton p)
| TT_abs (S0 : Ty n) (body : Tm (S n))
    (T : Ty (S n)) (C : CaptureSet n) :
    TermTy (CtxSnoc Gamma S0) body T
      (CUnion (capture_weaken C) (CSingleton (PVar FZ))) ->
    TyWf Gamma S0 -> CaptureWf Gamma C ->
    TermTy Gamma (TmAbs S0 body) (TyCapt C (ShFun S0 T)) CEmpty
| TT_app (p q : Path n) (Cfun Cp Cq : CaptureSet n)
    (S0 : Ty n) (T : Ty (S n)) :
    TermTy Gamma (TmPath p) (TyCapt Cfun (ShFun S0 T)) Cp ->
    TermTy Gamma (TmPath q) S0 Cq ->
    TermTy Gamma (TmApp p q) (ty_open T q) (CUnion Cp Cq)
| TT_pair (y z : Fin n) (a : Name) :
    TermTy Gamma (TmPair y a (DefVal z))
      (TyCapt
        (CUnion (CSingleton (PVar y)) (CSingleton (PVar z)))
        (ShPair
          (TyCapt (CSingleton (PVar y)) (ShSingle (PVar y))) a
          (TauTerm
            (TyCapt (CSingleton (path_weaken (PVar z)))
              (ShSingle (path_weaken (PVar z)))))))
      CEmpty
| TT_type_pair (y : Fin n) (a : Name) (shape : Shape n) :
    ShapeWf Gamma shape ->
    TermTy Gamma (TmPair y a (DefType shape))
      (TyCapt (CSingleton (PVar y))
        (ShPair
          (TyCapt (CSingleton (PVar y)) (ShSingle (PVar y))) a
          (TauType (shape_weaken shape) (shape_weaken shape))))
      CEmpty
| TT_capture_pair (y : Fin n) (a : Name) (C : CaptureSet n) :
    CaptureWf Gamma C ->
    TermTy Gamma (TmPair y a (DefCapture C))
      (TyCapt (CSingleton (PVar y))
        (ShPair
          (TyCapt (CSingleton (PVar y)) (ShSingle (PVar y))) a
          (TauCapture (capture_weaken C) (capture_weaken C))))
      CEmpty
| TT_let (bound : Tm n) (body : Tm (S n))
    (T U : Ty n) (C : CaptureSet n) :
    TermTy Gamma bound T C ->
    TermTy (CtxSnoc Gamma T) body (ty_weaken U) (capture_weaken C) ->
    TyWf Gamma U -> CaptureWf Gamma C ->
    TermTy Gamma (TmLet bound body) U C
| TT_sub (term : Tm n) (S0 T : Ty n) (C D : CaptureSet n) :
    TermTy Gamma term S0 C -> TySub Gamma S0 T ->
    CaptureSub Gamma C D -> TyWf Gamma T -> CaptureWf Gamma D ->
    TermTy Gamma term T D.

Arguments TermTy {n} Gamma _ _ _.

Print Assumptions TermTy.
