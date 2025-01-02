module SourceParser

open System.Reflection.Metadata
open FSharpx
open SourceExp
open SExpLexer

type Parser<'A> = SExp -> Result<'A, Lazy<string>>
type Parsoid<'A> = SExp list -> Result<'A * SExp list, Lazy<string>>
type Matcher<'A> = SExp -> 'A option
let matcher (p : Parser<'A>) : Matcher<'A> = Option.ofResult << p
let (|Matcher|_|) = matcher

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

let (<||>) (f : 'A -> Result<'B, 'C>) (g : 'A -> Result<'B, 'C>) : 'A -> Result<'B, 'C> =
    fun x ->
        match f x with
        | Ok _ as res -> res
        | _ -> g x

module Result =
    let seqMap f = List.map f >> Result.sequence

open Result

let errExpected exp act : Result<'T, Lazy<string>> =
    lazy $"Expected %s{exp}, got %A{act}" |> Error

module rec TyP =
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

    let tupleP : Parser<Ty> =
        function
        | SCurlList (SId "Tuple" :: rest) -> Ty.Tuple <!> seqMap p rest
        | s -> errExpected "<tuple type>" s

    let arrowP : Parser<Ty> =
        function
        | SParList (SOp "->" :: List.Snoc (args, ret)) -> curry Ty.Arrow <!> seqMap p args <*> p ret
        | s -> errExpected "<arrow type>" s

    let namedP : Parser<NamedTy> =
        intP <||> boolP <||> qualP <||> idP <||> appP <||> errExpected "<type name>"

    let p : Parser<Ty> =
        tupleP <||> arrowP <||> (namedP >> map Ty.Named) <||> errExpected "<type>"

module rec ExpP =
    let idExpP : Parser<IdExp> =
        function
        | SId x -> Ok (None, x)
        | SDotList [ SId x ] -> Ok (None, x)
        | SDotList (List.Snoc (t, SId x)) -> tuple2 <!> (Some <!> TyP.namedP (SDotList t)) <*> Ok x
        | s -> errExpected "<variable>" s

    let varP : Parser<Exp> = idExpP >> map Exp.Var

    let litIntP : Parser<Exp> =
        function
        | SInt i -> Ok (Exp.LitInt i)
        | s -> errExpected "<int>" s

    let (|Bool|_|) =
        function
        | SHash "true" -> Some true
        | SHash "false" -> Some false
        | _ -> None

    let litBoolP : Parser<Exp> =
        function
        | Bool b -> Ok (Exp.LitBool b)
        | s -> errExpected "<bool>" s

    let (|UnPrim|_|) : Matcher<UnaryPrim> =
        function
        | SOp "-" -> Some PrimNeg
        | SOp "~" -> Some PrimNot
        | _ -> None

    let unOpP : Parser<Exp> =
        function
        | SParList [ UnPrim prim ; x ] -> curry Exp.UnOp prim <!> p x
        | s -> errExpected "(<UnPrim> <expr>)" s

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

    let binOpP : Parser<Exp> =
        function
        | SParList [ BinPrim prim ; x ; y ] -> curry3 Exp.BinOp prim <!> p x <*> p y
        | s -> errExpected "(<BinPrim> <expr> <expr>)" s

    let formalList : SExp list -> Result<(Id * Ty) list, Lazy<string>> =
        List.map (
            function
            | SSqrList [ SId x ; SOp ":" ; Matcher TyP.p t ] -> Ok (x, t)
            | s -> errExpected "[<id> : <ty>]" s
        )
        >> sequence

    let lamP : Parser<Exp> =
        function
        | SParList [ SId "lambda" ; SParList formals ; body ] -> curry Exp.Lam <!> formalList formals <*> p body
        | s -> errExpected "<lambda>" s

    let tupleP : Parser<Exp> =
        function
        | SParList (SId "tuple" :: args) -> Exp.Tuple <!> sequence (List.map p args)
        | s -> errExpected "<tuple creation>" s

    let patternP : Parser<MatchPattern> =
        function
        | SId "_" -> Ok Ignored
        | SId var -> Ok (MatchVar var)
        | SInt i -> Ok (MatchLitInt i)
        | Bool b -> Ok (MatchLitBool b)
        | SParList (SId "tuple" :: rest) -> MatchTuple <!> sequence (List.map patternP rest)
        | SParList [ SId "name" ; SId var ; pat ] -> curry MatchNamed var <!> patternP pat
        | SParList (SId caseName :: rest) -> curry MatchCase caseName <!> sequence (List.map patternP rest)
        | s -> errExpected "<pattern>" s

    let caseP : Parser<MatchPattern * Exp> =
        function
        | SSqrList [ pattern ; SOp "=>" ; exp ] -> tuple2 <!> patternP pattern <*> p exp
        | s -> errExpected "<switch case>" s

    let switchP : Parser<Exp> =
        function
        | SParList (SId "switch" :: matchee :: cases) ->
            result {
                let! matchee = p matchee
                let! cases = sequence (List.map caseP cases)
                return curry Exp.Switch matchee cases
            }
        | s -> errExpected "<switch expression>" s

    let bindingP : Parser<SourceBinding> =
        function
        | SSqrList [ SId x ; v ] -> curry SourceBinding.Val x <!> p v
        | s -> errExpected "[<id> <exp>]" s

    let letP : Parser<Exp> =
        function
        | SParList [ SId "let" ; SParList bindings ; body ] ->
            curry Exp.Let <!> sequence (List.map bindingP bindings) <*> p body
        | s -> errExpected "(let <bindings> <body>)" s

    let genericAppP : Parser<Exp> =
        function
        | SParList (Matcher idExpP fn :: SCurlList genericArgs :: args) ->
            curry3 Exp.GenericApp fn <!> sequence (List.map TyP.p genericArgs)
            <*> sequence (List.map p args)
        | s -> errExpected "<generic function application>" s

    let appP : Parser<Exp> =
        function
        | SParList (fn :: args) -> curry Exp.App <!> p fn <*> sequence (List.map p args)
        | s -> errExpected "<function application>" s

    let p : Parser<Exp> =
        varP
        <||> litIntP
        <||> litBoolP
        <||> unOpP
        <||> binOpP
        <||> lamP
        <||> tupleP
        <||> switchP
        <||> letP
        <||> genericAppP
        <||> appP
        <||> errExpected "<exp>"

module rec TypeDefinitionP =
    let visibilityP : Parser<Visibility> =
        function
        | SId "public" -> Ok Public
        | SId "private" -> Ok Private
        | s -> errExpected "public | private" s

    type Deflets<'Contents> =
        {
            tyConstraints : TypeConstraint list
            contents : 'Contents list
            staticMethods : StaticMethod list
            containedTypes : TypeDefinition list
        }

    module Deflets =
        let zero =
            {
                tyConstraints = []
                contents = []
                staticMethods = []
                containedTypes = []
            }

        let plus a b =
            {
                tyConstraints = a.tyConstraints @ b.tyConstraints
                contents = a.contents @ b.contents
                staticMethods = a.staticMethods @ b.staticMethods
                containedTypes = a.containedTypes @ b.containedTypes
            }

        let tyConstraint x t =
            { zero with tyConstraints = [ (x, t) ] }

        let content c = { zero with contents = [ c ] }
        let staticMethod m = { zero with staticMethods = [ m ] }
        let containedType t = { zero with containedTypes = [ t ] }

    let nameWithOptionalTyFormalsP : Parser<Id * Id list> =
        function
        | SId name -> Ok (name, [])
        | SCurlList (SId name :: tyArgs) ->
            List.map
                (function
                | SId t -> Ok t
                | s -> errExpected "<identifier>" s)
                tyArgs
            |> sequence
            |> map (tuple2 name)
        | s -> errExpected "<id> | {<id> ...}" s

    let fieldP : Parser<Field> =
        function
        | SParList [ SId "let" ; vis ; SId name ; SOp ":" ; ty ] -> Field.mk name <!> visibilityP vis <*> TyP.p ty
        | s -> errExpected "(let <id> : <ty>)" s

    let caseP : Parser<EnumCase> =
        function
        | SParList (SId "case" :: SId name :: tys) -> EnumCase.mk name <!> sequence (List.map TyP.p tys)
        | s -> errExpected "(case <id> ...)" s

    let defletP (contentP : Parser<'C>) : Parser<Deflets<'C>> =
        function
        | SParList [ SId "where" ; SId tName ; SOp ":" ; t ] -> Deflets.tyConstraint tName <!> TyP.p t
        | SParList [ SId "static"
                     vis
                     SId "func"
                     SParList (name :: List.Snoc (List.Snoc (args, SOp "->"), retTy))
                     body ] ->
            result {
                let! vis = visibilityP vis
                let! name, tyFormals = nameWithOptionalTyFormalsP name

                let! formals =
                    (List.map
                        (function
                        | SSqrList [ SId name ; SOp ":" ; ty ] -> tuple2 name <!> TyP.p ty
                        | s -> errExpected "[<id> : <type>]" s)
                        args)
                    |> sequence

                let! retTy = TyP.p retTy
                let! body = ExpP.p body

                return
                    Deflets.staticMethod
                        {
                            name = name
                            visibility = vis
                            tyFormals = tyFormals
                            formals = formals
                            retTy = retTy
                            body = body
                        }
            }
        | SParList (SId "struct" :: _) as s -> Deflets.containedType <!> p s
        | SParList (SId "enum" :: _) as s -> Deflets.containedType <!> p s
        | s -> Deflets.content <!> (contentP <||> errExpected "<structlet>") s

    let private defHelperP<'C>
        (vis : SExp)
        (name : SExp)
        (contentP : Parser<'C>)
        (eject : 'C list -> TypeDefinitionContents)
        (deflets : SExp list)
        : Result<TypeDefinition, Lazy<string>>
        =
        result {
            let! vis = visibilityP vis
            let! name, tyFormals = nameWithOptionalTyFormalsP name

            let! deflets =
                List.map (defletP contentP) deflets
                |> sequence
                |> map (List.fold Deflets.plus Deflets.zero)

            return
                {
                    name = name
                    tyFormals = tyFormals
                    visibility = vis
                    constraints = deflets.tyConstraints
                    contents = eject deflets.contents
                    containedTypes = deflets.containedTypes
                    staticMethods = deflets.staticMethods
                }
        }

    let structP : Parser<TypeDefinition> =
        function
        | SParList (SId "struct" :: vis :: name :: deflets) -> defHelperP vis name fieldP StructFields deflets
        | s -> errExpected "(struct public|private ...)" s

    let enumP : Parser<TypeDefinition> =
        function
        | SParList (SId "enum" :: vis :: name :: deflets) -> defHelperP vis name caseP EnumCases deflets
        | s -> errExpected "(struct public|private ...)" s

    let p : Parser<TypeDefinition> =
        function
        | SParList (SId "struct" :: _) as s -> structP s
        | SParList (SId "enum" :: _) as s -> enumP s
        | s -> errExpected "(struct ...) | (enum ...)" s

let topLevelP (ss : SExp list) : Result<TypeDefinition list, Lazy<string>> =
    sequence (List.map TypeDefinitionP.p ss)
