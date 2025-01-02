[<AutoOpen>]
module Utils

open FSharpx

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

type Threesult<'A, 'B, 'C> =
    | Ok of 'A
    | Recoverable of 'B
    | Error of 'C

module Threesult =
    let (<||>) (f : 'A -> Threesult<'B, 'C, 'D>) (g : 'A -> Threesult<'B, 'C, 'D>) : 'A -> Threesult<'B, 'C, 'D> =
        fun x ->
            match f x with
            | Ok _ as res -> res
            | _ -> g x

    let sequence<'A, 'B, 'C> : Threesult<'A, 'B, 'C> list -> Threesult<'A list, 'B, 'C> =
        let rec loop acc =
            function
            | [] -> Ok (List.rev acc)
            | Ok a :: rest -> loop (a :: acc) rest
            | Recoverable r :: _ -> Recoverable r
            | Error e :: _ -> Error e

        loop []

    let seqMap f = List.map f >> sequence

    let toOptionOrFatal =
        function
        | Ok a -> Some a
        | Recoverable _ -> None
        | Error e -> failwith (string e)

    let trimap f g h =
        function
        | Ok a -> Ok (f a)
        | Recoverable r -> Recoverable (g r)
        | Error e -> Error (h e)

    let map f = trimap f id id
    let mapRecoverable f = trimap id f id
    let mapError f = trimap id id f
    let iter (f : 'a -> unit) = trimap f id id >> ignore
    let unwrap =
        function
            | Ok x -> x
            | res -> failwith $"unwrapped %A{res}"

    let bind f r =
        match r with
        | Ok x -> f x
        | Recoverable r -> Recoverable r
        | Error e -> Error e

    let ap f x = bind (flip map x) f

    let (<!>) = map
    let (<*>) = ap
    let (<!!>) f (x, y) = curry f <!> x <*> y
    let (<!!!>) f (x, y, z) = curry3 f <!> x <*> y <*> z

    type ThreesultBuilder() =
        member inline _.Return x = Ok x
        member inline _.Bind (m, [<InlineIfLambda>] f) = bind f m
        member inline _.ReturnFrom m = m
        member inline _.Zero () = Ok ()
        member inline _.Delay f = f
        member inline _.Run ([<InlineIfLambda>] f) = f ()

        member inline this.TryWith (m, [<InlineIfLambda>] h) =
            try
                this.ReturnFrom m
            with e ->
                h e

        member inline this.TryFinally (m, [<InlineIfLambda>] compensation) =
            try
                this.ReturnFrom m
            finally
                compensation ()

        member inline this.Using (res : #System.IDisposable, [<InlineIfLambda>] body) =
            this.TryFinally (
                body res,
                fun () ->
                    if not (isNull (box res)) then
                        res.Dispose ()
            )

        member inline this.While ([<InlineIfLambda>] guard, [<InlineIfLambda>] f) =
            while guard () do
                f () |> ignore

            this.Zero ()

        member inline this.For (sequence : seq<_>, [<InlineIfLambda>] body) =
            this.Using (
                sequence.GetEnumerator (),
                fun enum -> this.While (enum.MoveNext, this.Delay (fun () -> body enum.Current))
            )

    let threesult = ThreesultBuilder ()
