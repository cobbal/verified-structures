module SourceParser

open FSharpx
open SourceExp
open SExpLexer

type Parser<'A> = SExp -> Result<'A, Lazy<string>>
type Matcher<'A> = SExp -> 'A option
let matcher : Parser<'A> -> Matcher<'A> = (<<) Option.ofResult

module List =
    let unsnoc l =
        let rec loop acc x =
            function
            | [] -> (List.rev acc, x)
            | y :: xs -> loop (x :: acc) y xs

        match l with
        | [] -> None
        | x :: xs -> Some (loop [] x xs)

    let (|Snoc|_|) = unsnoc

module Result =
    let (<||>) (x : Result<'A, 'B>) (y : Result<'A, 'B>) : Result<'A, 'B> =
        match x with
        | Ok _ -> x
        | _ -> y

    let seqMap f = List.map f >> Result.sequence

let errExpected exp act : Result<'T, Lazy<string>> =
    lazy $"Expected %s{exp}, got %A{act}" |> Error

module rec TyP =
    open Result
    type P = Parser<Ty>

    let intP : Parser<NamedTy> =
        function
        | SHash "Int" -> Ok NamedTy.Int
        | s -> errExpected "#Int" s

    let boolP : Parser<NamedTy> =
        function
        | SHash "Bool" -> Ok NamedTy.Bool
        | s -> errExpected "#Bool" s

    let qualP : Parser<NamedTy> =
        function
        | SDotList [ x ] -> namedP x
        | SDotList (x :: xs) -> curry NamedTy.Qual <!> namedP x <*> namedP (SDotList xs)
        | s -> errExpected "<qualified type>" s

    let idP : Parser<NamedTy> =
        function
        | SId s -> Ok (NamedTy.Id s)
        | s -> errExpected "<type name>" s

    let appP : Parser<NamedTy> =
        function
        | SCurlList (f :: args) -> curry NamedTy.App <!> namedP f <*> seqMap p args
        | s -> errExpected "<type application>" s

    let namedP : Parser<NamedTy> =
        fun s -> intP s <||> boolP s <||> qualP s <||> idP s <||> appP s <||> errExpected "<type name>" s

    let tupleP : Parser<Ty> =
        function
        | SCurlList (SId "Tuple" :: rest) -> Ty.Tuple <!> seqMap p rest
        | s -> errExpected "<tuple type>" s

    let arrowP : Parser<Ty> =
        function
        | SParList (SOp "->" :: List.Snoc (args, ret)) -> curry Ty.Arrow <!> seqMap p args <*> p ret
        | s -> errExpected "<arrow type>" s

    let p : P = fun s -> tupleP s <||> arrowP s <||> (Ty.Named <!> namedP s) <||> errExpected "<type>" s

module rec ExpP =
    open Result
    type P = Parser<Exp>

    let varP : P =
        function
        | SDotList [ SId x ] -> Ok (Exp.Var (None, x))
        | SDotList (List.Snoc (t, SId x)) -> curry Exp.Var <!> (Some <!> TyP.namedP (SDotList t)) <*> Ok x
        | s -> errExpected "<variable>" s

    let litIntP : P =
        function
        | SInt i -> Ok (Exp.LitInt i)
        | s -> errExpected "<int>" s

    let libBoolP : P =
        function
        | SHash "true" -> Ok (Exp.LitBool true)
        | SHash "false" -> Ok (Exp.LitBool false)
        | s -> errExpected "<bool>" s

    let (|UnPrim|_|) : Matcher<UnaryPrim> =
        function
        | SOp "-" -> Some PrimNeg
        | SOp "~" -> Some PrimNot
        | _ -> None

    let unOpP : P =
        function
        | SParList [ UnPrim prim; x ] -> curry Exp.UnOp prim <!> p x
        | _ -> errExpected ""

    let (|BinPrim|_|) : Matcher<BinaryPrim> =
        function
        | SOp "+" -> Some PrimAdd
        | SOp "-" -> Some PrimSub
        | SOp "*" -> Some PrimMul
        | SOp "/" -> Some PrimDiv
        | SOp "%" -> Some PrimRem
        | SOp "=" -> Some PrimEq
        | SOp "!=" -> Some PrimNe
        | SOp "<" -> Some PrimLt
        | SOp ">" -> Some PrimGt
        | SOp "<=" -> Some PrimLe
        | SOp ">=" -> Some PrimGe
        | SOp "&&" -> Some PrimAnd
        | SOp "||" -> Some PrimOr
        | _ -> None


    let p: P = undefined
