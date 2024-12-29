module Program

open FSharpx.IO
open SExpLexer
open FSharpx
open FSharpx.Text

let parseFile filename =
    readFile filename |> List.ofSeq |> Strings.joinLines |> parse filename

parseFile "../miniswift-source/LeftistHeap.miniswift" |> printfn "%A"
