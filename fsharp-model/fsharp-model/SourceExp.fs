module SourceExp

type Id = string

[<RequireQualifiedAccess>]
type Ty =
    | Named of NamedTy
    | Tuple of Ty list
    | Arrow of formals : Ty list * ret : Ty

and NamedTy =
    | Int
    | Bool
    | Qual of NamedTy * NamedTy
    | Id of Id
    | App of tyName : NamedTy * tyArgs : Ty list

module Ty =
    let Int = Ty.Named <| NamedTy.Int
    let Bool = Ty.Named <| NamedTy.Bool
    let Qual a b = Ty.Named <| NamedTy.Qual (a, b)
    let Id x = Ty.Named <| NamedTy.Id x
    let App x args = Ty.Named <| NamedTy.App (x, args)

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
    | PrimEq
    | PrimNe
    | PrimLt
    | PrimGt
    | PrimLe
    | PrimGe
    (* bool * bool -> bool *)
    | PrimAnd
    | PrimOr

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
        | PrimOr -> (Ty.Bool, Ty.Bool, Ty.Bool)

[<RequireQualifiedAccess>]
type Exp =
    | Var of IdExp
    | LitInt of int32
    | LitBool of bool
    | UnOp of prim : UnaryPrim * arg0 : Exp
    | BinOp of prim : BinaryPrim * arg0 : Exp * arg1 : Exp
    | Lam of formals : (Id * Ty) list * body : Exp
    | Tuple of Exp list
    | Switch of matchee : Exp * cases : (MatchPattern * Exp) list
    | Let of bindings : SourceBinding list * body : Exp
    | GenericApp of f : IdExp * tyArgs : Ty list * args : Exp list
    | App of f : Exp * args : Exp list
    | Unreachable

and IdExp = NamedTy option * Id

and SourceBinding =
    // | Ty of id : Id * ty : Ty
    | Val of id : Id * exp : Exp

and MatchPattern =
    | Ignored
    | MatchVar of Id
    | MatchLitInt of int32
    | MatchLitBool of bool
    | MatchTuple of MatchPattern list
    | MatchNamed of Id * MatchPattern
    | MatchCase of Id * MatchPattern list

type Visibility =
    | Public
    | Private

type StaticMethod =
    {
        name : Id
        visibility : Visibility
        tyFormals : Id list
        formals : (Id * Ty) list
        retTy : Ty
        body : Exp
    }

type Field =
    {
        name : Id
        visibility : Visibility
        ty : Ty
    }

module Field =
    let mk x v t = { name = x ; visibility = v ; ty = t }

type EnumCase =
    {
        name : Id
        associatedValues : Ty list
    }

module EnumCase =
    let mk x vs = { name = x ; associatedValues = vs }

type TypeConstraint = Id * Ty

type TypeDefinitionContents =
    | EnumCases of EnumCase list
    | StructFields of Field list

type TypeDefinition =
    {
        name : Id
        tyFormals : Id list
        visibility : Visibility
        constraints : TypeConstraint list
        containedTypes : TypeDefinition list
        staticMethods : StaticMethod list
        contents : TypeDefinitionContents
    }
