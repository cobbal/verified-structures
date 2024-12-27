module Program

open SExpLexer

lex "(+ 123456 2 a-thing ((#true)))" |> Seq.iter (printfn "%A")
