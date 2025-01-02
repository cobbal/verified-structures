module Program

open FSharpx.IO
open SExpLexer
open FSharpx
open FSharpx.Text

let parseFile filename =
    let sexp =
        readFile filename
        |> List.ofSeq
        |> Strings.joinLines
        |> SExp.parse filename
    sexp
    |>! printfn "sexp: %A"
    |> SourceParser.topLevelP
    |> Threesult.mapRecoverable _.Value
    |>! printfn "sourceexp: %A"
    |> Threesult.unwrap
    |> List.map SourceParser.TypeDefinitionP.print
    |>! List.iter (printfn "%A")
    |>! List.iter2 SExp.assertEq sexp

parseFile "../miniswift-source/LeftistHeap.miniswift" |> ignore
