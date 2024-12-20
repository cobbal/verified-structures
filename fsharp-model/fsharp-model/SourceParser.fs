module SourceParser

open SourceExp
open FParsec

let idP : Parser<Id, unit> = identifier (IdentifierOptions())

module TyP =
    let varP : Parser<Ty, unit> = idP |>> Ty.Var
    let intP : Parser<Ty, unit> = pstring "Int" >>% Ty.Int
    let boolP : Parser<Ty, unit> = pstring "Bool" >>% Ty.Bool
