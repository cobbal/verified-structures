Require Import ZArith.
Require Import List.
Require Import String.

Open Scope list.

Inductive Ty : Type :=
| TyVar (α : string)
| TyInt
| TyBool
| TyTuple (τs : list Ty)
| TyArr (αs : list string) (τas : list Ty) (τr : Ty)
| TyExists (α: string) (τ: Ty)
.

Definition Env a := list (string * a).

Fixpoint lookup {a} (e : Env a) (x : string) : option a :=
  match e with
  | nil => None
  | cons (x', τ) e' =>
    if string_dec x x'
    then Some τ
    else lookup e' x
  end.

Inductive WF : forall (Δ : list string) (τ : Ty), Prop :=
| WFVar {Δ} (x : string) : In x Δ -> WF Δ (TyVar x)
| WFInt {Δ} : WF Δ TyInt
| WFBool {Δ} : WF Δ TyBool
| WFTuple {Δ} (τs : list Ty) : Forall (WF Δ) τs -> WF Δ (TyTuple τs)
| WFArr {Δ} (αs : list string) (τas : list Ty) (τr : Ty) :
  Forall (WF (αs ++ Δ)) (τr :: τas) ->
  WF Δ (TyArr αs τas τr)
| WFExists {Δ} α τ :
  WF (α :: Δ) τ ->
  WF Δ (TyExists α τ)
.

Definition WFEnv Δ : Env Ty -> Prop :=
  Forall (fun xτ => WF Δ (snd xτ)).

Inductive UnPrim :=
| PNeg
| PNot
.

Inductive BinPrim :=
(* Z -> Z -> Z *)
| PAdd | PSub | PMul | PDiv | PRem
(* Z -> Z -> bool *)
| PLt | PEq | PGt | PLe | PNe | PGe
(* bool -> bool -> bool *)
| PAnd | POr | PXor
.

Definition UnPrimArg (op : UnPrim) : Ty :=
  match op with
  | PNeg => TyInt
  | PNot => TyBool
  end.

Definition BinPrimArg0 (op : BinPrim) : Ty :=
  match op with
  | PAdd | PSub | PMul | PDiv | PRem
  | PLt | PEq | PGt | PLe | PNe | PGe => TyInt
  | PAnd | POr | PXor => TyBool
  end.
Definition BinPrimArg1 := BinPrimArg0.

Definition UnPrimRet (op : UnPrim) : Ty :=
  match op with
  | PNeg => TyInt
  | PNot => TyBool
  end.

Definition BinPrimRet (op : BinPrim) : Ty :=
  match op with
  | PAdd | PSub | PMul | PDiv | PRem => TyInt
  | PLt | PEq | PGt | PLe | PNe | PGe => TyBool
  | PAnd | POr | PXor => TyBool
  end.

Inductive SourceExpr : Type :=
| ELitInt (i : Z)
| ELitBool (b : bool)
| EVar (x : string)
| EUnOp (op : UnPrim) (arg : SourceExpr)
| EBinOp (op : BinPrim) (arg0 arg1 : SourceExpr)
| ELam (αs : list string) (formals : list (string * Ty)) (body : SourceExpr)
| EApp (f : SourceExpr) (τs : list Ty) (args : list SourceExpr)
| ETup (es : list SourceExpr)
| EProj (i : nat) (e: SourceExpr)
| EIf (eCond eThen eElse : SourceExpr)
| EPack (τ : Ty) (body : SourceExpr) (α : string) (τbody : Ty)
| EUnpack (α x : string) (e body : SourceExpr)
| ELet (binds : list SourceBinding)
with SourceBinding : Type :=
| BindVal (x : string) (τ : Ty) (e : SourceExpr)
| BindTy (α : string) (τ : Ty)
.

Inductive TypedList {X} (P : X -> Type) : list X -> Type :=
| tnil : TypedList P nil
| tcons {t ts} : P t -> TypedList P ts -> TypedList P (t :: ts)
.

Fixpoint envRemove {A} (xs : list string) (Γ : Env A) : Env A :=
  match Γ with
  | nil => nil
  | (x, v) :: Γ' =>
      if in_dec string_dec x xs
      then envRemove xs Γ'
      else (x, v) :: envRemove xs Γ'
  end.

Fixpoint tySubst (Γ : Env Ty) (τ : Ty) : Ty :=
  match τ with
  | TyVar x =>
      match lookup Γ x with
      | Some τ' => τ'
      | None => TyVar x
      end
  | TyInt => TyInt
  | TyBool => TyBool
  | TyTuple τs => TyTuple (map (tySubst Γ) τs)
  | TyArr αs τas τr => TyArr αs (map (tySubst (envRemove αs Γ)) τas) (tySubst (envRemove αs Γ) τr)
  | TyExists α τbody => TyExists α (tySubst (envRemove (α :: nil) Γ) τbody)
  end.

Fixpoint boundΔ (binds : list SourceBinding) : list string :=
  match binds with
  | nil => nil
  | BindVal _ _ _ :: binds' => boundΔ binds'
  | BindTy α _ :: binds' => α :: boundΔ binds'
  end.

Fixpoint boundΓ (binds : list SourceBinding) : list (string * Ty) :=
  match binds with
  | nil => nil
  | BindVal x τ _ :: binds' => (x, τ) :: boundΓ binds'
  | BindTy _ _ :: binds' => boundΓ binds'
  end.

Inductive TCExpr : forall (Δ : list string) (Γ : Env Ty) (τ : Ty), Type :=
| TCLitInt {Δ Γ} (i : nat) : TCExpr Δ Γ TyInt
| TCLitBool {Δ Γ} (b : bool) : TCExpr Δ Γ TyBool
| TCVar {Δ Γ} (x : string) {τ} {HWF : WF Δ τ} {H : lookup Γ x = Some τ} : TCExpr Δ Γ τ
| TCUnOp {Δ Γ} (op : UnPrim) :
  TCExpr Δ Γ (UnPrimArg op) ->
  TCExpr Δ Γ (UnPrimRet op)
| TCBinOp {Δ Γ} (op : BinPrim) :
  TCExpr Δ Γ (BinPrimArg0 op) ->
  TCExpr Δ Γ (BinPrimArg1 op) ->
  TCExpr Δ Γ (BinPrimRet op)
| TCLam {Δ Γ τr} (αs : list string) (formals : list (string * Ty)) :
  WFEnv (αs ++ Δ) formals ->
  TCExpr (αs ++ Δ) (formals ++ Γ) τr ->
  TCExpr Δ Γ (TyArr αs (map snd formals) τr)
| TCApp Δ Γ (tyArgs : list (string * Ty)) τas τr:
  Forall (WF Δ) (map snd tyArgs) ->
  TCExpr Δ Γ (TyArr (map fst tyArgs) τas τr) ->
  TypedList (TCExpr Δ Γ) (map (tySubst tyArgs) τas) ->
  TCExpr Δ Γ τr
| TCTup Δ Γ τs :
  TypedList (TCExpr Δ Γ) τs ->
  TCExpr Δ Γ (TyTuple τs)
| TCProj Δ Γ τs τ (i : nat) :
  TCExpr Δ Γ (TyTuple τs) ->
  nth_error τs i = Some τ ->
  TCExpr Δ Γ τ
| TCIf Δ Γ τ:
  TCExpr Δ Γ TyBool ->
  TCExpr Δ Γ τ ->
  TCExpr Δ Γ τ ->
  TCExpr Δ Γ τ
| TCPack Δ Γ τ α τbody :
  TCExpr Δ Γ (tySubst ((α, τ) :: nil) τbody) ->
  TCExpr Δ Γ (TyExists α τbody)
| TCUnpack Δ Γ α x τin τ :
  WF Δ τ ->
  TCExpr Δ Γ (TyExists α τin) ->
  TCExpr (α :: Δ) ((x, τin) :: Γ) τ ->
  TCExpr Δ Γ τ
| TCBind Δ Γ τ Δ' Γ' :
  TypedList (fun α => {τ | WF (Δ' ++ Δ) τ}) Δ' ->
  TypedList (fun xτ => TCExpr (Δ' ++ Δ) (Γ' ++ Γ) (snd xτ)) Γ' ->
  (* TypedList (TCTyBinding (Δ' ++ Δ)) Δ' -> *)
  (* TypedList (TCValBinding (Δ' ++ Δ) (Γ' ++ Γ)) Γ' ->  *)
  TCExpr (Δ' ++ Δ) (Γ' ++ Γ) τ ->
  TCExpr Δ Γ τ
(* with TCTyBinding : forall (Δ : list string) (α : string), Type := *)
(* | TCTyBind Δ α τ : WF Δ τ -> TCTyBinding Δ α *)
(* with TCValBinding : forall (Δ : list string) (Γ : Env Ty) (xτ : string * Ty), Type := *)
(* | TCValBind Δ Γ x τ : TCExpr Δ Γ τ -> TCValBinding Δ Γ (x, τ) *)
.

Inductive Value : forall (τ : Ty), Type :=
| VInt (i : nat) : Value TyInt
| VBool (b : bool) : Value TyBool
| VClo {Γ τr} (ρ : TCEnv Γ) (αs : list string) (formals : list (string * Ty)) :
  WFEnv αs formals ->
  TCExpr αs formals τr ->
  Value (TyArr αs (map snd formals) τr)
| VTup τs : TypedList Value τs -> Value (TyTuple τs)
| VPack α τ τbody : Value (tySubst ((α, τ) :: nil) τbody) -> Value (TyExists α τbody)
with TCEnv : forall (Γ : Env Ty), Type :=
| TCENil : TCEnv nil
| TCECons x {Γ τ} : Value τ -> TCEnv Γ -> TCEnv ((x, τ) :: Γ)
.

Reserved Notation "'EVAL' δ , ρ , σ ⊢ e ⇓ v , σ'" (at level 69, e at level 99, no associativity).
Inductive eval (δ : Env Ty) (ρ : Env addr) (σ : store) : forall {Δ Γ τ} (e : TCExpr Δ Γ τ) (v : Value τ)
 where "'EVAL' δ , ρ , σ ⊢ e ⇓ v , σ'" := (@eval δ ρ σ _ e v σ')
