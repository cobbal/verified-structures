module SourceExp

type Id = string

[<RequireQualifiedAccess>]
type Ty =
    | Var of Id
    | App of tyName : Id * tyArgs : Ty list
    | Int
    | Bool
    | Tuple of Ty list
    | Arrow of formals : Ty list * ret : Ty

type MethodTy =
    {
        // TODO: bounded quantification
        tyFormals : Id list
        formals : Ty list
        returnTy : Ty
    }

type UnaryPrim =
    (* int -> int *)
    | PrimNeg
    (* bool -> bool *)
    | PrimNot

    member this.Types : arg0 : Ty * ret : Ty =
        match this with
        | PrimNeg -> (Ty.Int, Ty.Int)
        | PrimNot -> (Ty.Bool, Ty.Bool)

type BinaryPrim =
    (* int * int -> int *)
    | PrimAdd
    | PrimSub
    | PrimMul
    | PrimDiv
    | PrimRem
    (* int * int -> bool *)
    | PrimLt
    | PrimEq
    | PrimGt
    | PrimLe
    | PrimNe
    | PrimGe
    (* bool * bool -> bool *)
    | PrimAnd
    | PrimOr
    | PrimXor

    member this.Types : arg0 : Ty * arg1 : Ty * ret : Ty =
        match this with
        | PrimAdd
        | PrimSub
        | PrimMul
        | PrimDiv
        | PrimRem -> (Ty.Int, Ty.Int, Ty.Int)
        | PrimLt
        | PrimEq
        | PrimGt
        | PrimLe
        | PrimNe
        | PrimGe -> (Ty.Int, Ty.Int, Ty.Bool)
        | PrimAnd
        | PrimOr
        | PrimXor -> (Ty.Bool, Ty.Bool, Ty.Bool)

[<RequireQualifiedAccess>]
type Exp =
    | Var of Id
    | LitInt of int32
    | LitBool of bool
    | UnOp of prim : UnaryPrim * arg0 : Exp
    | BinOp of prim : BinaryPrim * arg0 : Exp * arg1 : Exp
    | Lam of formals : (Id * Ty) list * body : Exp
    | App of f : Exp * tyArgs : Ty list * args : Exp list
    | Tuple of Exp list
    | TupleProj of i : int * exp : Exp
    | EnumMatch of matchee : Exp * cases : (MatchPattern * Exp) list
    | Let of bindings : SourceBinding list * body : Exp
    | Unreachable

and SourceBinding =
    | Ty of id : Id * ty : Ty
    | Val of id : Id * exp : Exp

and MatchPattern =
    | Ignored
    | MatchVar of Id
    | MatchLitInt of int32
    | MatchLitBool of bool
    | MatchTuple of MatchPattern list
    | MatchCase of Id * MatchPattern list
    | MatchNamed of MatchPattern * Id

type StaticMethod =
    {
        name : Id
        tyFormals : Id list
        formals : (Id * Ty) list
        body : Exp
    }

type EnumCase =
    {
        name : Id
        associatedValues : Ty list
    }

type Enum =
    {
        name : Id
        tyFormals : Id list
        cases : EnumCase list
        staticMethods : StaticMethod list
    }

type Struct =
    {
        name : Id
        tyFormals : Id list
        fields : (Id * Ty) list
        staticMethods : StaticMethod list
    }
