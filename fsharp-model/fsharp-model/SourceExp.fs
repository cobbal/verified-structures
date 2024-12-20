module SourceExp

type Id = string

[<RequireQualifiedAccess>]
type Ty =
    | Var of Id
    | Int
    | Bool
    | Tuple of Ty list
    | Arrow of tyFormals : Id list * formals : Ty list * ret : Ty
    | TyApp of Ty * Ty list
and GTy =
    | Ty of Ty

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
type SourceExp =
    | Var of Id
    | LitInt of int32
    | LitBool of bool
    | Unit
    | UnOp of prim : UnaryPrim * arg0 : SourceExp
    | BinOp of prim : BinaryPrim * arg0 : SourceExp * arg1 : SourceExp
    | Lam of tyFormals : Id list * formals : (Id * Ty) list * body : SourceExp
    | App of f : SourceExp * tyArgs : Ty list * args : SourceExp list
    | Tuple of SourceExp list
    | TupleProj of i : int * exp : SourceExp
    | EnumMatch of matchee : SourceExp * cases : (MatchPattern * SourceExp) list
    | If of cond : SourceExp * then_ : SourceExp * else_ : SourceExp
    | Let of bindings : SourceBinding list * body : SourceExp
    | Unreachable

and SourceBinding =
    | Ty of id : Id * ty : Ty
    | Val of id : Id * exp : SourceExp

and MatchPattern =
    | Ignored
    | Var of Id
    | LitInt of int32
    | LitBool of bool
    | Unit
    | Tuple of MatchPattern list
    | Case of Id * MatchPattern list
    | Named of MatchPattern * Id

type Method = {
    name : Id
    tyFormals : Id list
    formals : (Id * Ty) list
    body : SourceExp
}

type EnumCase = {
    name : Id
    associatedValues : Ty list
}

type Enum = {
    name : Id
    tyFormals : Id list
    cases : EnumCase list
    methods : Method list
}
