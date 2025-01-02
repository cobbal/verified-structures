module SourceParser

open FSharpx
open SourceExp
open SExpLexer

type PResult<'A> = Threesult<'A, Lazy<string>, string>
type Parser<'A> = SExp -> PResult<'A>
type Printer<'A> = 'A -> SExp
type Matcher<'A> = SExp -> 'A option
let matcher (p : Parser<'A>) : Matcher<'A> = Threesult.toOptionOrFatal << p
let (|Matcher|_|) = matcher

let recoverableExpected exp act : PResult<'A> =
    lazy $"Expected %s{exp}, got %A{act}" |> Recoverable

let errExpected exp act : PResult<'A> =
    $"Expected %s{exp}, got %A{act}" |> Error

open Threesult

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
        | SDotList (x :: xs) -> NamedTy.Qual <!!> (namedP x, namedP (SDotList xs))
        | s -> errExpected "<qualified type>" s

    let idP : Parser<NamedTy> =
        function
        | SId s -> Ok (NamedTy.Id s)
        | s -> errExpected "<type name>" s

    let appP : Parser<NamedTy> =
        function
        | SCurlList (f :: args) -> NamedTy.App <!!> (namedP f, seqMap parse args)
        | s -> errExpected "<type application>" s

    let tupleP : Parser<Ty> =
        function
        | SCurlList (SId "Tuple" :: rest) -> Ty.Tuple <!> seqMap parse rest
        | s -> errExpected "{Tuple ... }" s

    let arrowP : Parser<Ty> =
        function
        | SCurlList (SOp "->" :: List.Snoc (args, ret)) -> Ty.Arrow <!!> (seqMap parse args, parse ret)
        | s -> errExpected "{-> ... <type>}" s

    let namedP : Parser<NamedTy> =
        intP <||> boolP <||> qualP <||> idP <||> appP <||> errExpected "<type name>"

    let printNamed : Printer<NamedTy> =
        function
        | NamedTy.Int -> SHash "Int"
        | NamedTy.Bool -> SHash "Bool"
        | NamedTy.Qual _ as q ->
            let rec dot acc =
                function
                | NamedTy.Qual (t0, t1) -> dot (printNamed t0 :: acc) t1
                | t -> List.rev (printNamed t :: acc)

            SDotList (dot [] q)
        | NamedTy.Id x -> SId x
        | NamedTy.App (f, args) -> SCurlList (printNamed f :: List.map print args)

    let parse : Parser<Ty> =
        tupleP <||> arrowP <||> (namedP >> map Ty.Named) <||> errExpected "<type>"

    let print : Printer<Ty> =
        function
        | Ty.Named named -> printNamed named
        | Ty.Tuple tys -> SCurlList (SId "Tuple" :: List.map print tys)
        | Ty.Arrow (args, ret) -> SCurlList (SOp "->" :: List.map print (args @ [ ret ]))

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

    let printUnaryPrim : Printer<UnaryPrim> =
        function
        | PrimNeg -> SOp "-"
        | PrimNot -> SOp "~"

    let unOpP : Parser<Exp> =
        function
        | SParList [ UnPrim prim ; x ] -> Exp.UnOp <!!> (Ok prim, parse x)
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
        | SParList [ BinPrim prim ; x ; y ] -> Exp.BinOp <!!!> (Ok prim, parse x, parse y)
        | s -> errExpected "(<BinPrim> <expr> <expr>)" s

    let printBinaryPrim : Printer<BinaryPrim> =
        function
        | PrimAdd -> SOp "+"
        | PrimSub -> SOp "-"
        | PrimMul -> SOp "*"
        | PrimDiv -> SOp "/"
        | PrimRem -> SOp "%"
        | PrimEq -> SOp "="
        | PrimNe -> SOp "!="
        | PrimLt -> SOp "<"
        | PrimGt -> SOp ">"
        | PrimLe -> SOp "<="
        | PrimGe -> SOp ">="
        | PrimAnd -> SOp "&&"
        | PrimOr -> SOp "||"

    let formalList : SExp list -> PResult<(Id * Ty) list> =
        List.map (
            function
            | SSqrList [ SId x ; SOp ":" ; Matcher TyP.parse t ] -> Ok (x, t)
            | s -> errExpected "[<id> : <ty>]" s
        )
        >> sequence

    let lamP : Parser<Exp> =
        function
        | SParList [ SId "lambda" ; SParList formals ; body ] -> Exp.Lam <!!> (formalList formals, parse body)
        | s -> errExpected "<lambda>" s

    let tupleP : Parser<Exp> =
        function
        | SParList (SId "tuple" :: args) -> Exp.Tuple <!> sequence (List.map parse args)
        | s -> errExpected "<tuple creation>" s

    let patternP : Parser<MatchPattern> =
        function
        | SId "_" -> Ok Ignored
        | SId var -> Ok (MatchVar var)
        | SInt i -> Ok (MatchLitInt i)
        | Bool b -> Ok (MatchLitBool b)
        | SParList (SId "tuple" :: rest) -> MatchTuple <!> sequence (List.map patternP rest)
        | SParList [ SId "name" ; SId var ; pat ] -> MatchNamed <!!> (Ok var, patternP pat)
        | SParList (SId caseName :: rest) -> MatchCase <!!> (Ok caseName, sequence (List.map patternP rest))
        | s -> errExpected "<pattern>" s

    let caseP : Parser<MatchPattern * Exp> =
        function
        | SSqrList [ pattern ; SOp "=>" ; exp ] -> tuple2 <!> patternP pattern <*> parse exp
        | s -> errExpected "<switch case>" s

    let switchP : Parser<Exp> =
        function
        | SParList (SId "switch" :: matchee :: cases) ->
            Exp.Switch <!!> (parse matchee, sequence (List.map caseP cases))
        | s -> errExpected "<switch expression>" s

    let bindingP : Parser<SourceBinding> =
        function
        | SSqrList [ SId x ; SOp "=" ; v ] -> SourceBinding.Val <!!> (Ok x, parse v)
        | s -> errExpected "[<id> <exp>]" s

    let letP : Parser<Exp> =
        function
        | SParList [ SId "let" ; SParList bindings ; body ] ->
            Exp.Let <!!> (sequence (List.map bindingP bindings), parse body)
        | s -> errExpected "(let <bindings> <body>)" s

    let genericAppP : Parser<Exp> =
        function
        | SParList (Matcher idExpP fn :: SCurlList genericArgs :: args) ->
            Exp.GenericApp
            <!!!> (Ok fn, sequence (List.map TyP.parse genericArgs), sequence (List.map parse args))
        | s -> errExpected "<generic function application>" s

    let appP : Parser<Exp> =
        function
        | SParList (fn :: args) -> Exp.App <!!> (parse fn, sequence (List.map parse args))
        | s -> errExpected "<function application>" s

    let unreachableP : Parser<Exp> =
        function
        | SHash "unreachable" -> Ok Exp.Unreachable
        | s -> errExpected "#unreachable" s

    let parse : Parser<Exp> =
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
        <||> unreachableP
        <||> errExpected "<exp>"

    let printFormal (x, ty) =
        SSqrList [ SId x ; SOp ":" ; TyP.print ty ]

    let printIdExp : Printer<IdExp> =
        function
        | None, x -> SId x
        | Some ty, x ->
            match TyP.printNamed ty with
            | SDotList l -> SDotList (l @ [ SId x ])
            | t -> SDotList [ t ; SId x ]

    let print : Printer<Exp> =
        function
        | Exp.Var v -> printIdExp v
        | Exp.LitInt i -> SInt i
        | Exp.LitBool true -> SHash "true"
        | Exp.LitBool false -> SHash "false"
        | Exp.UnOp (p, e) -> SParList [ printUnaryPrim p ; print e ]
        | Exp.BinOp (p, e0, e1) -> SParList [ printBinaryPrim p ; print e0 ; print e1 ]
        | Exp.Lam (formals, body) -> SParList [ SId "lambda" ; SParList (List.map printFormal formals) ; print body ]
        | Exp.Tuple exps -> SParList (SId "tuple" :: List.map print exps)
        | Exp.Switch (matchee, cases) ->
            let rec printPat =
                function
                | Ignored -> SId "_"
                | MatchVar x -> SId x
                | MatchLitInt i -> SInt i
                | MatchLitBool true -> SHash "true"
                | MatchLitBool false -> SHash "false"
                | MatchTuple pats -> SParList (SId "tuple" :: List.map printPat pats)
                | MatchNamed (var, pat) -> SParList [ SId "name" ; SId var ; printPat pat ]
                | MatchCase (caseName, pats) -> SParList (SId caseName :: List.map printPat pats)

            let printCase (pat, body) =
                SSqrList [ printPat pat ; SOp "=>" ; print body ]

            SParList (SId "switch" :: print matchee :: List.map printCase cases)
        | Exp.Let (bindings, body) ->
            let printBinding (SourceBinding.Val (x, e)) = SSqrList [ SId x ; SOp "=" ; print e ]
            SParList [ SId "let" ; SParList (List.map printBinding bindings) ; print body ]
        | Exp.GenericApp (fn, tyArgs, args) ->
            SParList (printIdExp fn :: SCurlList (List.map TyP.print tyArgs) :: List.map print args)
        | Exp.App (fn, args) -> SParList (print fn :: List.map print args)
        | Exp.Unreachable -> SHash "unreachable"

module rec TypeDefinitionP =
    let visibilityP : Parser<Visibility> =
        function
        | SId "public" -> Ok Public
        | SId "private" -> Ok Private
        | s -> errExpected "public | private" s

    let printVisibility : Printer<Visibility> =
        function
        | Public -> SId "public"
        | Private -> SId "private"

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
        | SParList [ SId "let" ; vis ; SId name ; SOp ":" ; ty ] -> Field.mk name <!> visibilityP vis <*> TyP.parse ty
        | s -> errExpected "(let <id> : <ty>)" s

    let caseP : Parser<EnumCase> =
        function
        | SParList (SId "case" :: SId name :: tys) -> EnumCase.mk name <!> sequence (List.map TyP.parse tys)
        | s -> errExpected "(case <id> ...)" s

    let defletP (contentP : Parser<'C>) : Parser<Deflets<'C>> =
        function
        | SParList [ SId "where" ; SId tName ; SOp ":" ; t ] -> Deflets.tyConstraint tName <!> TyP.parse t
        | SParList [ SId "static"
                     vis
                     SId "func"
                     SParList (name :: List.Snoc (List.Snoc (args, SOp "->"), retTy))
                     body ] ->
            threesult {
                let! vis = visibilityP vis
                let! name, tyFormals = nameWithOptionalTyFormalsP name

                let! formals =
                    (List.map
                        (function
                        | SSqrList [ SId name ; SOp ":" ; ty ] -> tuple2 name <!> TyP.parse ty
                        | s -> errExpected "[<id> : <type>]" s)
                        args)
                    |> sequence

                let! retTy = TyP.parse retTy
                let! body = ExpP.parse body

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
        | SParList (SId "struct" :: _) as s -> Deflets.containedType <!> parse s
        | SParList (SId "enum" :: _) as s -> Deflets.containedType <!> parse s
        | s -> Deflets.content <!> (contentP <||> errExpected "<structlet>") s

    let printConstraint : Printer<TypeConstraint> =
        fun (x, ty) -> SParList [ SId "where" ; SId x ; SOp ":" ; TyP.print ty ]

    let printGenericName name tyFormals =
        if List.isEmpty tyFormals then
            SId name
        else
            SCurlList (SId name :: List.map SId tyFormals)

    let methodPrint : Printer<StaticMethod> =
        fun m ->
            SParList
                [
                    SId "static"
                    printVisibility m.visibility
                    SId "func"
                    SParList (
                        printGenericName m.name m.tyFormals :: List.map ExpP.printFormal m.formals
                        @ [ SOp "->" ; TyP.print m.retTy ]
                    )
                    ExpP.print m.body
                ]

    let private defHelperP<'C>
        (vis : SExp)
        (name : SExp)
        (contentP : Parser<'C>)
        (eject : 'C list -> TypeDefinitionContents)
        (deflets : SExp list)
        : PResult<TypeDefinition>
        =
        threesult {
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

    let parse : Parser<TypeDefinition> =
        function
        | SParList (SId "struct" :: _) as s -> structP s
        | SParList (SId "enum" :: _) as s -> enumP s
        | s -> errExpected "(struct ...) | (enum ...)" s

    let print : Printer<TypeDefinition> =
        fun d ->
            let form, contents =
                match d.contents with
                | EnumCases cases ->
                    "enum",
                    cases
                    |> List.map (fun case ->
                        SParList (SId "case" :: SId case.name :: List.map TyP.print case.associatedValues)
                    )
                | StructFields fields ->
                    "struct",
                    fields
                    |> List.map (fun field ->
                        SParList
                            [
                                SId "let"
                                printVisibility field.visibility
                                SId field.name
                                SOp ":"
                                TyP.print field.ty
                            ]
                    )

            seq {
                yield SId form
                yield printVisibility d.visibility
                yield printGenericName d.name d.tyFormals
                yield! Seq.map printConstraint d.constraints
                yield! Seq.map print d.containedTypes
                yield! contents
                yield! Seq.map methodPrint d.staticMethods
            }
            |> List.ofSeq
            |> SParList

let topLevelP (ss : SExp list) : PResult<TypeDefinition list> =
    sequence (List.map TypeDefinitionP.parse ss)
