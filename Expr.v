Require Import ZArith.
Require Import List.
Require Import String.

Inductive Ty : Type :=
| TyVar (α : string)
| TyInt
| TyBool
| TyTuple (τs : list Ty)
| TyArr (xs : list string) (τas : list Ty) (τr : Ty)
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
| WFArr {Δ} (xs : list string) (τas : list Ty) (τr : Ty) :
  Forall (WF (xs ++ Δ)) (τr :: τas) ->
  WF Δ (TyArr xs τas τr)
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
| ELam (τs : list string) (formals : list (string * Ty)) (body : SourceExpr)
| EApp (f : SourceExpr) (τs : list Ty) (args : list SourceExpr)
| ETup (es : list SourceExpr)
| EProj (i : nat) (e: SourceExpr)
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

Fixpoint subst (Γ : Env Ty) (τ : Ty) : Ty :=
  match τ with
  | TyVar x =>
      match lookup Γ x with
      | Some τ' => τ'
      | None => TyVar x
      end
  | TyInt => TyInt
  | TyBool => TyBool
  | TyTuple τs => TyTuple (map (subst Γ) τs)
  | TyArr xs τas τr => TyArr xs (map (subst (envRemove xs Γ)) τas) (subst (envRemove xs Γ) τr)
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
| TCLam {Δ Γ τr} (xs : list string) (formals : list (string * Ty)) :
  WFEnv (xs ++ Δ) formals ->
  TCExpr (xs ++ Δ) (formals ++ Γ) τr ->
  TCExpr Δ Γ (TyArr xs (map snd formals) τr)
| TCApp Δ Γ (tyArgs : list (string * Ty)) τas τr:
  Forall (WF Δ) (map snd tyArgs) ->
  TCExpr Δ Γ (TyArr (map fst tyArgs) τas τr) ->
  TypedList (TCExpr Δ Γ) (map (subst tyArgs) τas) ->
  TCExpr Δ Γ τr
| TCTup Δ Γ τs :
  TypedList (TCExpr Δ Γ) τs ->
  TCExpr Δ Γ (TyTuple τs)
| TCProj Δ Γ τs τ (i : nat) :
  TCExpr Δ Γ (TyTuple τs) ->
  nth_error τs i = Some τ ->
  TCExpr Δ Γ τ
.
