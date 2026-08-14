From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Allocation metadata for a body and its source use set. *)
Inductive CapExactBody :
    forall {n : nat}, Store n -> Ty n -> Tm (S n) -> Ty (S n) ->
      CaptureSet (S n) -> Type :=
| CEB_source {n m : nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {S0 : Ty n} {body : Tm (S n)}
    {T : Ty (S n)} {C : CaptureSet (S n)} :
    TermTy (CtxSnoc Gamma S0) body T C ->
    CapExactBody sigma (ty_rename S0 rho) (tm_rename body (ext rho))
      (ty_rename T (ext rho)) (capture_rename C (ext rho)).

(** Introduction-rule capture set assigned to a value. *)
Inductive CapExactValue :
    forall {n : nat}, Store n -> Tm n -> CaptureSet n -> Type :=
| CEV_abs {n : nat} {sigma : Store n} {A : Ty n} {body : Tm (S n)}
    {B : Ty (S n)} {Q : CaptureSet n} :
    CapExactBody sigma A body B
      (CUnion (capture_weaken Q) (CSingleton (PVar FZ))) ->
    CapExactValue sigma (TmAbs A body) Q
| CEV_pair {n : nat} {sigma : Store n} {y z : Fin n} {a : Name} :
    CapExactValue sigma (TmPair y a (DefVal z))
      (CUnion (CSingleton (PVar y)) (CSingleton (PVar z)))
| CEV_type_pair {n : nat} {sigma : Store n} {y : Fin n} {a : Name}
    {W : Shape n} :
    CapExactValue sigma (TmPair y a (DefType W)) (CSingleton (PVar y))
| CEV_capture_pair {n : nat} {sigma : Store n} {y : Fin n} {a : Name}
    {W : CaptureSet n} :
    CapExactValue sigma (TmPair y a (DefCapture W)) (CSingleton (PVar y)).

(** A store carrying its exact introduction capture witness at each cell. *)
Inductive CapWorld : forall {n : nat}, Store n -> Type :=
| CapWorld_empty : CapWorld StoreEmpty
| CapWorld_val {n : nat} {sigma : Store n} {v : Tm n}
    {is_value : Tm_IsValue v} {Q : CaptureSet n}
    (world : CapWorld sigma) (exact : CapExactValue sigma v Q) :
    CapWorld (StoreVal sigma v is_value).

(** Lookup transports both stored values and their exact capture sets. *)
Inductive CapLookup :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Fin n -> Tm n -> CaptureSet n -> Type :=
| CapLookup_here {n : nat} {sigma : Store n} {v : Tm n}
    {is_value : Tm_IsValue v} {Q : CaptureSet n}
    {world : CapWorld sigma} {exact : CapExactValue sigma v Q} :
    CapLookup (CapWorld_val world exact (is_value := is_value)) FZ
      (tm_weaken v) (capture_weaken Q)
| CapLookup_there {n : nat} {sigma : Store n} {x : Fin n}
    {v u : Tm n} {is_value : Tm_IsValue u} {Q R : CaptureSet n}
    {world : CapWorld sigma} {exact : CapExactValue sigma u R} :
    CapLookup world x v Q ->
    CapLookup (CapWorld_val world exact (is_value := is_value)) (FS x)
      (tm_weaken v) (capture_weaken Q).

(** The eleven mutually recursive capture-aware evidence families. *)
Inductive CapEnvironment :
    forall {n m : nat} {sigma : Store m}, CapWorld sigma ->
      Ctx n -> Valuation n m -> Type :=
| CE_intro {n m : nat} {sigma : Store m} {world : CapWorld sigma}
    {Gamma : Ctx n} {rho : Valuation n m} :
    (forall x : Fin n,
      CapLocationEvidence world (apply rho x)
        (ty_rename (ctx_lookup Gamma x) rho)) ->
    CapEnvironment world Gamma rho
with CapLocationEvidence :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Fin n -> Ty n -> Type :=
| CLE_top {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {x : Fin n} {v : Tm n} {Q C : CaptureSet n} :
    CapLookup world x v Q -> CapRelation world Q C ->
    CapLocationEvidence world x (TyCapt C ShTop)
| CLE_fun {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {x : Fin n} {Q C : CaptureSet n} {A S0 : Ty n}
    {body : Tm (S n)} {B U : Ty (S n)} :
    CapLookup world x (TmAbs A body) Q ->
    CapBody world A body B
      (CUnion (capture_weaken Q) (CSingleton (PVar FZ))) ->
    CapTyCoercion world S0 A ->
    CapDeferredCoercion world S0 B U ->
    CapRelation world Q C ->
    CapLocationEvidence world x (TyCapt C (ShFun S0 U))
| CLE_pair {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {x y : Fin n} {Q C : CaptureSet n}
    {a : Name} {delta : Def n k} {S0 : Ty n} {d : Tau (S n) k} :
    CapLookup world x (TmPair y a delta) Q ->
    CapLocationEvidence world y S0 ->
    CapRealizes world (def_referent delta) (tau_open d (PVar y)) ->
    CapRelation world Q C ->
    CapLocationEvidence world x (TyCapt C (ShPair S0 a d))
| CLE_single {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {x : Fin n} {v : Tm n} {Q C : CaptureSet n} {p : Path n} :
    CapLookup world x v Q ->
    PathResolve sigma p (RLoc x) -> CapRelation world Q C ->
    CapLocationEvidence world x (TyCapt C (ShSingle p))
| CLE_selection {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {x : Fin n} {v : Tm n} {Q C E : CaptureSet n}
    {p : Path n} {a : Name} {W : Shape n} :
    CapLookup world x v Q ->
    PathResolve sigma (PSel p a) (RType W) ->
    CapLocationEvidence world x (TyCapt E W) ->
    CapRelation world Q C ->
    CapLocationEvidence world x (TyCapt C (ShTSel p a))
with CapRealizes :
    forall {n : nat} {k : Kind} {sigma : Store n}, CapWorld sigma ->
      Referent n -> Tau n k -> Type :=
| CRZ_loc {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {x : Fin n} {T : Ty n} :
    CapLocationEvidence world x T ->
    CapRealizes world (RLoc x) (TauTerm T)
| CRZ_type {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {L W U : Shape n} :
    CapShapeCoercion world L W -> CapShapeCoercion world W U ->
    CapRealizes world (RType W) (TauType L U)
| CRZ_capture {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {L W U : CaptureSet n} :
    CapRelation world L W -> CapRelation world W U ->
    CapRealizes world (RCapture W) (TauCapture L U)
with CapRelation :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      CaptureSet n -> CaptureSet n -> Type :=
| CR_source {n m : nat} {sigma : Store m} {world : CapWorld sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {C D : CaptureSet n} :
    CapEnvironment world Gamma rho -> CaptureSub Gamma C D ->
    CapRelation world (capture_rename C rho) (capture_rename D rho)
| CR_refl {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C : CaptureSet n} : CapRelation world C C
| CR_trans {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C D E : CaptureSet n} :
    CapRelation world C D -> CapRelation world D E ->
    CapRelation world C E
| CR_runtime {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C D : CaptureSet n} :
    CaptureRuntimeConv (PathRuntimeEq sigma) C D ->
    CapRelation world C D
| CR_empty {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C : CaptureSet n} : CapRelation world CEmpty C
| CR_union_left {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C D : CaptureSet n} : CapRelation world C (CUnion C D)
| CR_union_right {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C D : CaptureSet n} : CapRelation world D (CUnion C D)
| CR_union_elim {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C D E : CaptureSet n} :
    CapRelation world C E -> CapRelation world D E ->
    CapRelation world (CUnion C D) E
| CR_alias {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p q : Path n} {x : Fin n} :
    PathResolve sigma p (RLoc x) -> PathResolve sigma q (RLoc x) ->
    CapRelation world (CSingleton q) (CSingleton p)
| CR_fold {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {x : Fin n} {v : Tm n} {Q : CaptureSet n} :
    PathResolve sigma p (RLoc x) -> CapLookup world x v Q ->
    CapRelation world Q (CSingleton p)
| CR_fst_root {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {x : Fin n} :
    PathResolve sigma (PFst p) (RLoc x) ->
    CapRelation world (CSingleton (PFst p)) (CSingleton p)
| CR_sel_root {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {a : Name} {x : Fin n} :
    PathResolve sigma (PSel p a) (RLoc x) ->
    CapRelation world (CSingleton (PSel p a)) (CSingleton p)
| CR_select_lower {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {a : Name} {L W : CaptureSet n} :
    PathResolve sigma (PSel p a) (RCapture W) ->
    CapRelation world L W -> CapRelation world L (CSelect p a)
| CR_select_upper {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {a : Name} {W U : CaptureSet n} :
    PathResolve sigma (PSel p a) (RCapture W) ->
    CapRelation world W U -> CapRelation world (CSelect p a) U
with CapTyCoercion :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Ty n -> Ty n -> Type :=
| CTC_refl {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {T : Ty n} : CapTyCoercion world T T
| CTC_trans {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {T U V : Ty n} :
    CapTyCoercion world T U -> CapTyCoercion world U V ->
    CapTyCoercion world T V
| CTC_runtime {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {T U : Ty n} :
    TyRuntimeConv (PathRuntimeEq sigma) T U -> CapTyCoercion world T U
| CTC_capt {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {C D : CaptureSet n} {S0 T : Shape n} :
    CapRelation world C D -> CapShapeCoercion world S0 T ->
    CapTyCoercion world (TyCapt C S0) (TyCapt D T)
with CapShapeCoercion :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Shape n -> Shape n -> Type :=
| CSC_refl {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 : Shape n} : CapShapeCoercion world S0 S0
| CSC_trans {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 T U : Shape n} :
    CapShapeCoercion world S0 T -> CapShapeCoercion world T U ->
    CapShapeCoercion world S0 U
| CSC_runtime {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 T : Shape n} :
    ShapeRuntimeConv (PathRuntimeEq sigma) S0 T ->
    CapShapeCoercion world S0 T
| CSC_bot {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 : Shape n} : CapShapeCoercion world ShBot S0
| CSC_top {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 : Shape n} : CapShapeCoercion world S0 ShTop
| CSC_widen {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {x : Fin n} {C : CaptureSet n} {S0 : Shape n} :
    PathResolve sigma p (RLoc x) ->
    CapLocationEvidence world x (TyCapt C S0) ->
    CapShapeCoercion world (ShSingle p) S0
| CSC_alias {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p q : Path n} {x : Fin n} :
    PathResolve sigma p (RLoc x) -> PathResolve sigma q (RLoc x) ->
    CapShapeCoercion world (ShSingle q) (ShSingle p)
| CSC_select_lower {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {a : Name} {L W : Shape n} :
    PathResolve sigma (PSel p a) (RType W) ->
    CapShapeCoercion world L W ->
    CapShapeCoercion world L (ShTSel p a)
| CSC_select_upper {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {p : Path n} {a : Name} {W U : Shape n} :
    PathResolve sigma (PSel p a) (RType W) ->
    CapShapeCoercion world W U ->
    CapShapeCoercion world (ShTSel p a) U
| CSC_fun {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 S' : Ty n} {T T' : Ty (S n)} :
    CapTyCoercion world S' S0 ->
    CapDeferredCoercion world S' T T' ->
    CapShapeCoercion world (ShFun S0 T) (ShFun S' T')
| CSC_pair {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {S0 S' : Ty n} {a : Name}
    {d d' : Tau (S n) k} :
    CapTyCoercion world S0 S' -> CapMemberClosure world S0 d d' ->
    CapShapeCoercion world (ShPair S0 a d) (ShPair S' a d')
with CapCoercion :
    forall {n : nat} {k : Kind} {sigma : Store n}, CapWorld sigma ->
      Tau n k -> Tau n k -> Type :=
| CC_refl {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {d : Tau n k} : CapCoercion world d d
| CC_trans {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {d e f : Tau n k} :
    CapCoercion world d e -> CapCoercion world e f ->
    CapCoercion world d f
| CC_runtime {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {d e : Tau n k} :
    TauRuntimeConv (PathRuntimeEq sigma) d e -> CapCoercion world d e
| CC_term {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {T U : Ty n} :
    CapTyCoercion world T U ->
    CapCoercion world (TauTerm T) (TauTerm U)
| CC_type {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {L U L' U' : Shape n} :
    CapShapeCoercion world L' L -> CapShapeCoercion world U U' ->
    CapCoercion world (TauType L U) (TauType L' U')
| CC_capture {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {L U L' U' : CaptureSet n} :
    CapRelation world L' L -> CapRelation world U U' ->
    CapCoercion world (TauCapture L U) (TauCapture L' U')
with CapDeferredCoercion :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Ty n -> Ty (S n) -> Ty (S n) -> Type :=
| CDC_refl {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 : Ty n} {T : Ty (S n)} : CapDeferredCoercion world S0 T T
| CDC_trans {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 : Ty n} {T U V : Ty (S n)} :
    CapDeferredCoercion world S0 T U ->
    CapDeferredCoercion world S0 U V ->
    CapDeferredCoercion world S0 T V
| CDC_runtime {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 : Ty n} {T U : Ty (S n)} :
    TyRuntimeConv (PathScopedLift (PathRuntimeEq sigma)) T U ->
    CapDeferredCoercion world S0 T U
| CDC_narrow {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {S0 S' : Ty n} {T U : Ty (S n)} :
    CapTyCoercion world S' S0 -> CapDeferredCoercion world S0 T U ->
    CapDeferredCoercion world S' T U
| CDC_source {n m : nat} {sigma : Store m} {world : CapWorld sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {S0 : Ty n}
    {T U : Ty (S n)} :
    CapEnvironment world Gamma rho -> TySub (CtxSnoc Gamma S0) T U ->
    CapDeferredCoercion world (ty_rename S0 rho)
      (ty_rename T (ext rho)) (ty_rename U (ext rho))
with CapMemberClosure :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Ty n -> forall {k : Kind}, Tau (S n) k -> Tau (S n) k -> Type :=
| CMC_source {n m : nat} {k : Kind} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    {S0 : Ty n} {d e : Tau (S n) k} :
    CapEnvironment world Gamma rho -> TauSub (CtxSnoc Gamma S0) d e ->
    CapMemberClosure world (ty_rename S0 rho)
      (tau_rename d (ext rho)) (tau_rename e (ext rho))
with CapBody :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Ty n -> Tm (S n) -> Ty (S n) -> CaptureSet (S n) -> Type :=
| CB_source {n m : nat} {sigma : Store m} {world : CapWorld sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {S0 : Ty n}
    {body : Tm (S n)} {T : Ty (S n)} {C : CaptureSet (S n)} :
    CapEnvironment world Gamma rho -> TermTy (CtxSnoc Gamma S0) body T C ->
    CapBody world (ty_rename S0 rho) (tm_rename body (ext rho))
      (ty_rename T (ext rho)) (capture_rename C (ext rho))
with CapValue :
    forall {n : nat} {sigma : Store n}, CapWorld sigma ->
      Tm n -> Ty n -> CaptureSet n -> Type :=
| CV_abs {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {A T : Ty n} {body : Tm (S n)} {B : Ty (S n)}
    {Q : CaptureSet n} :
    CapBody world A body B
      (CUnion (capture_weaken Q) (CSingleton (PVar FZ))) ->
    CapTyCoercion world (TyCapt Q (ShFun A B)) T ->
    CapValue world (TmAbs A body) T Q
| CV_pair {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {y z : Fin n} {a : Name} {T : Ty n} :
    CapTyCoercion world
      (TyCapt
        (CUnion (CSingleton (PVar y)) (CSingleton (PVar z)))
        (ShPair
          (TyCapt (CSingleton (PVar y)) (ShSingle (PVar y))) a
          (TauTerm
            (TyCapt (CSingleton (path_weaken (PVar z)))
              (ShSingle (path_weaken (PVar z))))))) T ->
    CapValue world (TmPair y a (DefVal z)) T
      (CUnion (CSingleton (PVar y)) (CSingleton (PVar z)))
| CV_type_pair {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {y : Fin n} {a : Name} {W : Shape n} {T : Ty n} :
    CapTyCoercion world
      (TyCapt (CSingleton (PVar y))
        (ShPair
          (TyCapt (CSingleton (PVar y)) (ShSingle (PVar y))) a
          (TauType (shape_weaken W) (shape_weaken W)))) T ->
    CapValue world (TmPair y a (DefType W)) T (CSingleton (PVar y))
| CV_capture_pair {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {y : Fin n} {a : Name} {W : CaptureSet n} {T : Ty n} :
    CapTyCoercion world
      (TyCapt (CSingleton (PVar y))
        (ShPair
          (TyCapt (CSingleton (PVar y)) (ShSingle (PVar y))) a
          (TauCapture (capture_weaken W) (capture_weaken W)))) T ->
    CapValue world (TmPair y a (DefCapture W)) T (CSingleton (PVar y)).

(** A valid world justifies every stored introduction capture set with the
    same value evidence used by the interpretation. *)
Inductive CapWorldValid :
    forall {n : nat} {sigma : Store n}, CapWorld sigma -> Type :=
| CWV_empty : CapWorldValid CapWorld_empty
| CWV_val {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {v : Tm n} {is_value : Tm_IsValue v} {T : Ty n}
    {Q : CaptureSet n} {exact : CapExactValue sigma v Q} :
    CapWorldValid world -> CapValue world v T Q ->
    CapWorldValid (CapWorld_val world exact (is_value := is_value)).

Print Assumptions CapEnvironment.
Print Assumptions CapValue.
Print Assumptions CapWorldValid.
