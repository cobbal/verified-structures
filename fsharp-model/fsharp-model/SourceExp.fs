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
    let int = Ty.Named <| NamedTy.Int
    let bool = Ty.Named <| NamedTy.Bool
    let qual a b = Ty.Named <| NamedTy.Qual (a, b)
    let id x = Ty.Named <| NamedTy.Id x
    let app x args = Ty.Named <| NamedTy.App (x, args)

type MethodTy =
    {
        // TODO: bounded quantification?
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
        | PrimNeg -> (Ty.int, Ty.int)
        | PrimNot -> (Ty.bool, Ty.bool)

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
        | PrimRem -> (Ty.int, Ty.int, Ty.int)
        | PrimLt
        | PrimEq
        | PrimGt
        | PrimLe
        | PrimNe
        | PrimGe -> (Ty.int, Ty.int, Ty.bool)
        | PrimAnd
        | PrimOr -> (Ty.bool, Ty.bool, Ty.bool)

[<RequireQualifiedAccess>]
type Exp<'T> =
    | Var of IdExp
    | LitInt of int32
    | LitBool of bool
    | UnOp of prim : UnaryPrim * arg0 : TExp<'T>
    | BinOp of prim : BinaryPrim * arg0 : TExp<'T> * arg1 : TExp<'T>
    | Lam of formals : (Id * Ty) list * body : TExp<'T>
    | Tuple of TExp<'T> list
    | Switch of matchee : TExp<'T> * cases : (MatchPattern * TExp<'T>) list
    | Let of bindings : SourceBinding<'T> list * body : TExp<'T>
    | GenericApp of f : IdExp * tyArgs : Ty list * args : TExp<'T> list
    | App of f : TExp<'T> * args : TExp<'T> list
    | Unreachable

and TExp<'T> = Exp<'T> * 'T
and IdExp = NamedTy option * Id

and SourceBinding<'T> =
    // | Ty of id : Id * ty : Ty
    | Val of id : Id * exp : TExp<'T>

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

type StaticMethod<'T> =
    {
        name : Id
        visibility : Visibility
        tyFormals : Id list
        formals : (Id * Ty) list
        retTy : Ty
        body : TExp<'T>
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

type TypeDefinition<'T> =
    {
        name : Id
        tyFormals : Id list
        visibility : Visibility
        constraints : TypeConstraint list
        containedTypes : TypeDefinition<'T> list
        staticMethods : StaticMethod<'T> list
        contents : TypeDefinitionContents
    }

type UExp = TExp<unit>
type USourceBinding = SourceBinding<unit>
type UStaticMethod = StaticMethod<unit>
type UTypeDefinition = TypeDefinition<unit>

module UExp =
    let private t (e : Exp<unit>) : UExp =  (e, ())
    let private u (e : UExp) = e
    let private us (e : UExp list) = e
    let var x = t <| Exp.Var x
    let litInt i = t <| Exp.LitInt i
    let litBool b = t <| Exp.LitBool b
    let unOp p e0 = t <| Exp.UnOp (p, u e0)
    let binOp p e0 e1 = t <| Exp.BinOp (p, u e0, u e1)
    let lam formals body = t <| Exp.Lam (formals, u body)
    let tuple l = t <| Exp.Tuple (us l)
    let switch matchee (cases : (MatchPattern * UExp) list) = t <| Exp.Switch (u matchee, cases)
    let let_ (bindings : USourceBinding list) body = t <| Exp.Let (bindings, u body)
    let genericApp f tyArgs args = t <| Exp.GenericApp (f, tyArgs, us args)
    let app f args = t <| Exp.App (u f, us args)
    let unreachable = t <| Exp.Unreachable
