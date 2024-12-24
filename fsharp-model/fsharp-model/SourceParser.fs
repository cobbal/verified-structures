module SourceParser

open SourceExp
open FParsec

type Parser<'t> = Parser<'t, unit>

let idP : Parser<Id> = identifier (IdentifierOptions ()) .>> spaces
let token s : Parser<unit> = skipString s
let tokenSp s : Parser<unit> = token s .>> spaces

let inParens (p : Parser<'a>) : Parser<'a list> =
    sepEndBy p (tokenSp ",") |> between (tokenSp "(") (tokenSp ")")

let inAngles (p : Parser<'a>) : Parser<'a list> =
    sepEndBy p (tokenSp ",") |> between (tokenSp "<") (tokenSp ">")

module TyP =
    type P = Parser<Ty>

    let rec varOrTyAppP () : P =
        idP .>>. opt (inAngles p)
        |>> function
            | x, Some tyArgs -> Ty.App (x, tyArgs)
            | x, None -> Ty.Var x

    and intP : P = tokenSp "Int" >>% Ty.Int
    and boolP : P = tokenSp "Bool" >>% Ty.Bool
    and tupleP () : P = inParens p |>> Ty.Tuple

    and arrowP () : P =
        inParens p .>> tokenSp "->" .>>. p |>> Ty.Arrow

    and p : P = choice [ varOrTyAppP () ; intP ; boolP ; tupleP () ; arrowP () ]

module ExpP =
    type P = Parser<Exp>

    // https://docs.swift.org/swift-book/documentation/the-swift-programming-language/summaryofthegrammar/
    let rec p : P = prefixP .>>. many1 infixP
    and prefixP : P = opt prefixOpP .>>. postfixP
    and infixP : P = infixOpP .>>. prefixP
    and primaryP : P = choice [
        idP .>>. opt genericArgsP
        literalP
        switchP
        closureP
        parenthesizedP
        tupleP
    ]
    and switchP : P =
        tokenSp "switch" >>.

    // let rec varP : P = idP |>> Exp.Var
    // and intP : P = pint32 .>> spaces |>> Exp.LitInt
    //
    // and boolP : P =
    //     choice [ tokenSp "true" >>% Exp.LitBool true ; tokenSp "false" >>% Exp.LitBool false ]
