module SExpLexer

open System.Diagnostics.Tracing
open FSharpx
open FSharpx.Collections

// Based on https://matt.might.net/articles/parsing-s-expressions-scala/
(*
  <file> ::= <s-exp-list>
  <s-exp> ::= <atom>
           |  '(' <s-exp-list> ')'
  <s-exp-list> ::= <sexp> <s-exp-list>
                |
  <atom> ::= <symbol>
          |  <integer>
          |  #t  |  #f
*)

// Exceptions.

type Exception =
    /// Thrown when code is not finished.
    | UnfinishedException
    /// Thrown when data is not convertible.
    | InconvertibleException
    /// Thrown when code reaches a supposedly impossible state -- a bug.
    | ImpossibleException
    /// Thrown when the input is not a valid S-Expression.
    | ParseException of reason : string

type SExp =
    | SInt of int
    | SBool of bool
    | SSymbol of string
    | SList of SExp list

// S-Expression lexer token types.
type SExpToken =
    | LPAR
    | RPAR
    | INT of int
    | HASH of string
    | ID of string
    | EOS

module Seq =
    let conj xs x = Seq.append xs [| x |]

type private LexState =
    | InComment
    | InId of char list
    | InHash of char list
    | InNum of char list
    | InWhitespace

let private (|Whitespace|_|) c =
    if System.Char.IsWhiteSpace c then Some c else None

let private (|Digit|_|) c =
    if System.Char.IsDigit c then Some c else None

let lex (input : char seq) : SExpToken seq =
    let emit =
        let strRev (l : char list) : string =
            Array.ofList l |> Array.rev |> System.String

        function
        | InComment -> seq { }
        | InId buf -> seq { buf |> strRev |> ID }
        | InHash buf -> seq { buf |> strRev |> HASH }
        | InNum buf -> seq { buf |> strRev |> System.Int32.Parse |> INT }
        | InWhitespace -> seq { }

    let rec processChar (state : LexState) (c : char) : SExpToken seq * LexState =
        match state with
        | InComment when c = '\n' -> seq { }, InWhitespace
        | InComment -> seq { }, InComment
        | InId buf ->
            match c with
            | Whitespace _ -> emit state, InWhitespace
            | ';' -> emit state, InComment
            | '(' -> Seq.conj (emit state) LPAR, InWhitespace
            | ')' -> Seq.conj (emit state) RPAR, InWhitespace
            | _ -> seq { }, InId (c :: buf)
        | InHash buf ->
            match c with
            | Whitespace _ -> emit state, InWhitespace
            | ';' -> emit state, InComment
            | '(' -> Seq.conj (emit state) LPAR, InWhitespace
            | ')' -> Seq.conj (emit state) RPAR, InWhitespace
            | _ -> seq { }, InHash (c :: buf)
        | InNum buf ->
            match c with
            | Digit _ -> seq { }, InNum (c :: buf)
            | _ ->
                let tokens, newState = processChar InWhitespace c
                Seq.append (emit state) tokens, newState
        | InWhitespace ->
            match c with
            | Whitespace _ -> seq { }, InWhitespace
            | Digit _ -> seq { }, InNum [ c ]
            | ';' -> seq { }, InComment
            | '#' -> seq { }, InHash []
            | '(' -> seq { LPAR }, InWhitespace
            | ')' -> seq { RPAR }, InWhitespace
            | _ -> seq { }, InId [ c ]

    let tokens, state =
        Seq.fold
            (fun (acc, state) c ->
                let tokens, newState = processChar state c
                (Seq.append acc tokens, newState)
            )
            (seq { }, InWhitespace)
            input

    seq {
        yield! tokens
        yield! emit state
        yield EOS
    }
