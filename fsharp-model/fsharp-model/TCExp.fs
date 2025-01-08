module TCExp

open SourceExp
open FSharpx

type TyBinding =
    | Type of Ty
    | Def of TypeDefinition<Ty>

type TyEnv =
    | TyEnv of Map<Id, TyBinding>

    member this.Raw =
        match this with
        | TyEnv m -> m

    member this.Extend (l : (Id * Ty) list) : TyEnv =
        List.fold (fun g (x, t) -> Map.add x (Type t) g) this.Raw l |> TyEnv

    member this.LookupTy (x : IdExp) : Ty =
        let rec loop x =
            match Map.TryFind this.Raw
        loop x

let rec inferType (tyEnv : TyEnv) : Exp<unit> -> TExp<Ty> =
    function
    | Exp.Var x -> (Exp.Var x, tyEnv.LookupTy x)
    | Exp.LitInt i -> (Exp.LitInt i, Ty.int)
    | Exp.LitBool b -> (Exp.LitBool b, Ty.bool)
    | Exp.UnOp (prim, (e0, ())) ->
        let t0, tr = prim.Types
        let e0 = checkType tyEnv e0 t0
        (Exp.UnOp (prim, e0), tr)
    | Exp.BinOp (prim, (e0, ()), (e1, ())) ->
        let t0, t1, tr = prim.Types
        let e0 = checkType tyEnv e0 t0
        let e1 = checkType tyEnv e1 t1
        (Exp.BinOp (prim, e0, e1), tr)
    | Exp.Lam (formals, (body, ())) ->
        let _, tr as body = inferType (tyEnv.Extend formals) body
        (Exp.Lam (formals, body), Ty.Arrow (List.map snd formals, tr))
    | Exp.Tuple es ->
        let tes = List.map (inferType tyEnv) (List.map fst es)
        (Exp.Tuple tes, Ty.Tuple (List.map snd tes))
    | Exp.Switch (matchee, cases) -> failwith "this is the hard one"
    | Exp.Let (bindings, (body, ())) ->
        let tyEnv, bindings =
            List.fold
                (fun (tyEnv, acc) (Val (x, (e, ()))) ->
                    let _, t as e = inferType tyEnv e
                    (Map.add (None, x) t tyEnv, Val (x, e) :: acc)
                )
                (tyEnv, [])
                bindings

        let body = inferType tyEnv body
        (Exp.Let (bindings, body), snd body)
    | Exp.GenericApp (f, tyArgs, args) ->
        let tf = Map.find f tyEnv
        undefined

and checkType (tyEnv : TyEnv) (e : Exp<unit>) (t : Ty) : TExp<Ty> =
    match e, t with
    | _ -> undefined
