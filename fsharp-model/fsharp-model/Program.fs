module Program

open FSharpx.IO
open SExpLexer
open FSharpx
open FSharpx.Text

let parseFile filename =
    readFile filename
    |> List.ofSeq
    |> Strings.joinLines
    |> parse filename
    |>! printfn "%A"
    |> SourceParser.topLevelP
    |> Result.mapError _.Value

parseFile "../miniswift-source/LeftistHeap.miniswift" |> printfn "%A"
