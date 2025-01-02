module SExpLexer

open FSharpx
open FSharpx.Text

// Loosely based on https://matt.might.net/articles/parsing-s-expressions-scala/

// S-Expression lexer token types.
type SExpToken =
    | LPAR
    | RPAR
    | LSQR
    | RSQR
    | LCURL
    | RCURL
    | DOT
    | INT of int
    | HASH of string
    | ID of string
    | OP of string

[<StructuredFormatDisplay("{filename}:{line}:{col}")>]
type Location =
    {
        filename : string
        line : int
        col : int
    }

    override this.ToString () =
        $"%s{this.filename}:%d{this.line}:%d{this.col}"

module Seq =
    let conj xs x = Seq.append xs [| x |]

let onFst (f : 'a -> 'c) : 'a * 'b -> 'c * 'b = fun (one, two) -> (f one, two)

let sequenceFirst (x : 'a) (thunk : unit -> unit) =
    thunk ()
    x

type private LexState =
    | InComment
    | InId of Location * char list
    | InHash of Location * char list
    | InOp of Location * char list
    | InNum of Location * char list
    | InWhitespace

let private (|Whitespace|_|) c = System.Char.IsWhiteSpace c
let private (|Digit|_|) c = System.Char.IsDigit c
let private (|Between|_|) lo hi c = lo <= c && c <= hi
let private (|OpChar|_|) = flip Set.contains (Set.ofSeq "/=-+!*%<>&|^~?:")

let private (|IdChar|_|) c =
    match c with
    | Between 'a' 'z'
    | Between 'A' 'Z'
    | Between '0' '9'
    | '_' -> true
    | _ -> false

let private markLocations filename (chars : char seq) : (Location * char) seq =
    let mutable line = 1
    let mutable col = 1

    seq {
        for c in chars do
            yield
                ({
                    filename = filename
                    line = line
                    col = col
                 },
                 c)

            if c = '\n' then
                line <- line + 1
                col <- 1
            else
                col <- col + 1
    }

let lex filename (input : char seq) : (Location * SExpToken) seq =
    let strRev (l : char list) : string =
        Array.ofList l |> Array.rev |> System.String

    let emit =
        function
        | InComment -> seq { }
        | InId (loc, buf) -> seq { strRev buf |> ID |> tuple2 loc }
        | InHash (loc, buf) -> seq { strRev buf |> HASH |> tuple2 loc }
        | InOp (loc, buf) -> seq { strRev buf |> OP |> tuple2 loc }
        | InNum (loc, buf) -> seq { strRev buf |> System.Int32.Parse |> INT |> tuple2 loc }
        | InWhitespace -> seq { }

    let rec processChar (state : LexState) (loc, c) : (Location * SExpToken) seq * LexState =
        match state, c with
        | InComment, '\n' -> Seq.empty, InWhitespace
        | InComment, _ -> Seq.empty, InComment
        | _, Whitespace -> emit state, InWhitespace
        | _, ';' -> emit state, InComment
        | _, '(' -> Seq.conj (emit state) (loc, LPAR), InWhitespace
        | _, ')' -> Seq.conj (emit state) (loc, RPAR), InWhitespace
        | _, '[' -> Seq.conj (emit state) (loc, LSQR), InWhitespace
        | _, ']' -> Seq.conj (emit state) (loc, RSQR), InWhitespace
        | _, '{' -> Seq.conj (emit state) (loc, LCURL), InWhitespace
        | _, '}' -> Seq.conj (emit state) (loc, RCURL), InWhitespace
        | _, '.' -> Seq.conj (emit state) (loc, DOT), InWhitespace
        | InId (loc, buf), IdChar -> Seq.empty, InId (loc, c :: buf)
        | InHash (loc, buf), IdChar -> Seq.empty, InHash (loc, c :: buf)
        | InOp (loc, buf), OpChar -> Seq.empty, InOp (loc, c :: buf)
        | InNum (loc, buf), Digit -> Seq.empty, InNum (loc, c :: buf)
        | InNum _, _ ->
            // let tokens, newState = processChar InWhitespace c
            // Seq.append (emit state) tokens, newState
            failwith $"%O{loc}: Expected digit, got %A{c}"
        | InWhitespace, '#' -> Seq.empty, InHash (loc, [])
        | InWhitespace, Digit -> Seq.empty, InNum (loc, [ c ])
        | InWhitespace, IdChar -> Seq.empty, InId (loc, [ c ])
        | InWhitespace, OpChar -> Seq.empty, InOp (loc, [ c ])
        | _, _ -> failwith $"%O{loc} invalid identifier character %A{c} (state {state})"

    let tokens, state =
        input
        |> markLocations filename
        |> Seq.fold (fun (acc, state) lc -> processChar state lc |> onFst (Seq.append acc)) (Seq.empty, InWhitespace)

    Seq.append tokens (emit state)

type SExp0 =
    | S0Int of int
    | S0Hash of string
    | S0Op of string
    | S0Id of string
    | S0Dot
    | S0ParList of SExp0 list
    | S0SqrList of SExp0 list
    | S0CurlList of SExp0 list

type EnumeratorWrapper<'T when 'T : equality>
    (enum : System.Collections.Generic.IEnumerator<'T>, current : 'T option ref)
    =
    new(s : 'T seq)
        =
        let enum = s.GetEnumerator ()
        EnumeratorWrapper (enum, ref <| (if enum.MoveNext () then Some enum.Current else None))

    member this.Peek () = current.Value

    member this.Pop () =
        let old = current.Value
        current.Value <- if enum.MoveNext () then Some enum.Current else None
        old

let parse0 (tokens : (Location * SExpToken) seq) : SExp0 list =
    let iter = EnumeratorWrapper tokens

    let eat expected =
        match iter.Pop () with
        | None -> failwith $"Parse error: expected %A{expected}, got EOF"
        | Some (_, actual) when actual = expected -> ()
        | Some (loc, actual) -> failwith $"%O{loc}: Parse error: expected %A{expected}, got %A{actual}"

    let rec parseSexp () =
        match iter.Pop () with
        | None -> failwith "Unexpected end of stream"
        | Some (_, ID s) -> S0Id s
        | Some (_, INT i) -> S0Int i
        | Some (_, HASH s) -> S0Hash s
        | Some (_, OP s) -> S0Op s
        | Some (_, LPAR) -> sequenceFirst (S0ParList (parseSexpSeq ())) (fun () -> eat RPAR)
        | Some (_, LSQR) -> sequenceFirst (S0SqrList (parseSexpSeq ())) (fun () -> eat RSQR)
        | Some (_, LCURL) -> sequenceFirst (S0CurlList (parseSexpSeq ())) (fun () -> eat RCURL)
        | Some (_, DOT) -> S0Dot
        | Some (loc, RPAR) -> failwith $"%O{loc}: Unexpected ')'"
        | Some (loc, RSQR) -> failwith $"%O{loc}: Unexpected ']'"
        | Some (loc, RCURL) -> failwith $"%O{loc}: Unexpected '}}'"

    and parseSexpSeq () =
        match iter.Peek () with
        | None
        | Some (_, RPAR)
        | Some (_, RSQR)
        | Some (_, RCURL) -> []
        | _ -> parseSexp () :: parseSexpSeq ()

    let result = parseSexpSeq ()

    match iter.Peek () with
    | None -> result
    | Some token -> failwith $"Unexpected %A{token}"

[<StructuredFormatDisplay("{DisplayText}")>]
type SExp =
    | SInt of int
    | SHash of string
    | SOp of string
    | SId of string
    | SDotList of SExp list
    | SParList of SExp list
    | SSqrList of SExp list
    | SCurlList of SExp list
    with
    member this.DisplayText =
        match this with
        | SInt i -> string i
        | SHash s -> "#" + s
        | SOp s -> s
        | SId s -> s
        | SDotList l -> l |> Seq.map string |> String.concat "."
        | SParList l -> $"(%s{l |> List.map string |> Strings.joinWords})"
        | SSqrList l -> $"[%s{l |> List.map string |> Strings.joinWords}]"
        | SCurlList l -> $"{{%s{l |> List.map string |> Strings.joinWords}}}"

let parse filename (input : char seq) : SExp list =
    let rec parse1 =
        function
        | S0Int i -> SInt i
        | S0Hash s -> SHash s
        | S0Op s -> SOp s
        | S0Id s -> SId s
        | S0Dot -> failwith "Unexpected '.'"
        | S0ParList l -> SParList (parseList l)
        | S0SqrList l -> SSqrList (parseList l)
        | S0CurlList l -> SCurlList (parseList l)

    and parseList =
        function
        | [] -> []
        | a :: S0Dot :: rest ->
            match parseList rest with
            | SDotList l :: xs -> SDotList (parse1 a :: l) :: xs
            | x :: xs -> SDotList [parse1 a; x] :: xs
            | [] -> failwith "Trailing '.' found"
        | a :: rest -> parse1 a :: parseList rest

    lex filename input |> parse0 |> parseList
