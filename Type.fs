module Type



open Log
open Lang
open Parser
open Pretty
open Extensions
open Combinators



type Scheme = Forall of string [] * Type



type SchemeEnv = Map<string, Scheme>



type TypeEnv = Map<string, Type>



type Substitution = Map<string, Type>



type Constraint =
  | Equal of Type * Type
  | OneOf of Type * Type []



// ++++++++++++++
// + TypeVarGen +
// ++++++++++++++



module TypeVarGen =
  let mutable _mNEXT_NAME = 'a', 1



  let reset () = _mNEXT_NAME <- 'a', 1



  let next () =
    let numToString =
      function
      | 1 -> ""
      | n -> string n

    match _mNEXT_NAME with
    | 'z', n ->
        _mNEXT_NAME <- 'a', n + 1

        "z" + numToString n
        |> TVar

    | c, n ->
        _mNEXT_NAME <- char ((int c) + 1), n

        string c + numToString n
        |> TVar



// ++++++++
// + Type +
// ++++++++



module Type =
  let unknownsToTypeVars =
    let rec go =
      function
      | TUnknown       -> TypeVarGen.next()
      | TList t        -> TList (go t)
      | TRef t         -> TRef (go t)
      | TFun ts        -> TFun (Array.map go ts)
      | TTuple ts      -> TTuple (Array.map go ts)
      | TArrow (t, t2) -> TArrow (Pair.map go (t, t2))
      | t              -> t

    go



  let renewTypeVarsAndReturnNames : Type -> Type * string [] =
    let unvar =
      function
      | TVar s -> s
      | t      -> failwithf "Error @ Type.renewTypeVarsAndReturnNames: %A" t

    let rec go ss =
      function
      | TVar s ->
          match Map.tryFind s ss with
          | Some tv -> tv, ss
          | None    ->
              let tv = TypeVarGen.next ()
              tv, Map.add s tv ss

      | TList  t  -> Pair.mapLeft TList  (go ss t)
      | TRef   t  -> Pair.mapLeft TRef   (go ss t)
      | TFun   ts -> Pair.mapLeft TFun   (Array.mapAccum go ss ts)
      | TTuple ts -> Pair.mapLeft TTuple (Array.mapAccum go ss ts)

      | TArrow (t, t2) ->
          let t3, ss2 = go ss  t
          let t4, ss3 = go ss2 t2
          TArrow (t3, t4), ss3

      | t -> t, ss

    go Map.empty
    >> Pair.mapRight (Map.values >> Array.ofSeq >> Array.map unvar)


  let canonicalize : Type -> Type =
    let rec go ss =
      function
      | TVar s ->
          match Map.tryFind s ss with
          | Some tv -> tv, ss
          | None    ->
              let tv = TypeVarGen.next ()
              tv, Map.add s tv ss

      | TList  t  -> Pair.mapLeft TList  (go ss t)
      | TRef   t  -> Pair.mapLeft TRef   (go ss t)
      | TFun   ts -> Pair.mapLeft TFun   (Array.mapAccum go ss ts)
      | TTuple ts -> Pair.mapLeft TTuple (Array.mapAccum go ss ts)

      | TArrow (t, t2) ->
          let t3, ss2 = go ss  t
          let t4, ss3 = go ss2 t2
          TArrow (t3, t4), ss3

      | t -> t, ss

    go Map.empty
    >> fst



  let ftv =
    let rec goMany ts =
      Array.map go ts
      |> Set.unionMany

    and go =
      function
      | TRef  t -> go t
      | TList t -> go t

      | TFun   ts -> goMany ts
      | TTuple ts -> goMany ts

      | TArrow (t, t2) ->
          Set.union (go t) (go t2)

      | TRecord (_, m) ->
          Map.toArray m
          |> Array.map snd
          |> goMany

      | TADT (_, m) ->
          Map.toArray m
          |> Array.map snd
          |> Array.concat
          |> goMany

      | TVar s -> Set.singleton s

      | _  -> Set.empty

    go



  let substitute (sub : Substitution) =
    let rec go =
      function
      | TVar s as t    -> Map.findWithDefault s t sub
      | TFun   ts      -> TFun (Array.map go ts)
      | TTuple ts      -> TTuple (Array.map go ts)
      | TList t        -> TList (go t)
      | TRef t         -> TRef (go t)
      | TArrow (t, t2) -> TArrow (Pair.map go (t, t2))
      | t              -> t

    go



// ++++++++++++++
// + Constraint +
// ++++++++++++++



module Constraint =
  let prettyString =
    function
    | Equal (t, t2) ->
        Type.prettyString t + " <=> " + Type.prettyString t2

    | OneOf (t, ts) ->
        Array.map Type.prettyString ts
        |> String.concat ", "
        |> sprintf "%s is one of [%s]" (Type.prettyString t)



  let prettyPrint =
    prettyString
    >> printfn "%s"



  let prettyPrintMany =
    Array.map (logWithI2 prettyString)
    >> ignore


  let substitute sub =
    function
    | Equal (t, t2) ->
        Pair.map (Type.substitute sub) (t, t2)
        |> Equal

    | OneOf (t, ts) ->
        Array.map (Type.substitute sub) ts
        |> Pair.leftRight (Type.substitute sub t)
        |> OneOf



// ++++++++++
// + Scheme +
// ++++++++++



module Scheme =
  let instantiate =
    function
    | Forall (ss, t) ->
        [ for s in ss do
            yield s, TypeVarGen.next()
        ] |> Map.ofSeq
          |> flip Type.substitute t



  let ofType t =
    Type.renewTypeVarsAndReturnNames t
    |> uncurry Pair.rightLeft
    |> Forall



  let ftv =
    function
    | Forall (ss, t) ->
        Set.difference (Type.ftv t) (Set.ofArray ss)



  let substitute (sub : Substitution) =
    function
    | Forall (ss, t) ->
        let sub2 = Array.fold (flip Map.remove) sub ss
        Forall (ss, Type.substitute sub2 t)



// +++++++++++
// + TypeEnv +
// +++++++++++



module TypeEnv =
  let ofSchemeEnv : SchemeEnv -> TypeEnv =
    Map.mapValues Scheme.instantiate



  let tryFindTypeWithField (s : string) (env : TypeEnv) =
    let f =
      function
      | TRecord (_, m) -> Map.containsKey s m
      | _              -> false

    Seq.tryFind f (Map.values env)



// +++++++++++++
// + SchemeEnv +
// +++++++++++++



module SchemeEnv =
  let empty : SchemeEnv = Map.empty



  let ofTypeEnv : TypeEnv -> SchemeEnv =
    Map.mapValues Scheme.ofType



  let tryFindTypeWithField (s : string) (env : SchemeEnv) =
    let f _ =
      function
      | Forall (_, (TRecord (_, m) as t)) when Map.containsKey s m -> Some t
      | _ -> None

    Map.tryPick f env



  let addType (s : string) t : SchemeEnv -> SchemeEnv =
    Map.add s (Forall ([||], t))



  let addTypes kvps env =
    Array.fold (flip (uncurry addType)) env kvps



  let ftv =
    Map.toSeq
    >> Seq.map (snd >> Scheme.ftv)
    >> Set.unionMany



  let generalize t =
    ftv
    >> Set.difference (Type.ftv t)
    >> Set.toArray
    >> Pair.rightLeft t
    >> Forall



  let tryFindType s =
    Map.tryFind s
    >> Option.map Scheme.instantiate



  let tryFindTypeOfConstructor s =
    let f =
      function
      | TADT (_, m) -> Map.exists (fun s2 _ -> s = s2) m
      | t -> false

    TypeEnv.ofSchemeEnv
    >> Map.tryFindByValue f
    >> Option.map snd



  let substitute sub env =
    Map.mapValues (Scheme.substitute sub) env



// ++++++++++++++++
// + Substitution +
// ++++++++++++++++



module Substitution =
  let empty = Map.empty



  let compose (sub : Substitution) (sub2 : Substitution) : Substitution =
    Map.union
      (Map.mapValues (Type.substitute sub) sub2)
      sub



// +++++++++
// + error +
// +++++++++



type TypeError =
  | UnboundVar                  of string
  | UndefinedType               of string
  | UndefinedConstructor        of string * Core
  | UndefinedConstructorPattern of string * Pattern
  | TypeAlreadyDefined          of string
  | ConstructorAlreadyDefined   of string
  | RecLitInvalidField          of string
  | RecLitMissingField          of string
  | RecLitDuplicateField        of string
  | UnificationMismatch         of Type [] * Type []
  | UnificationNotEqual         of Type * Type
  | UnificationNotOneOf         of Type * Type []
  | UnificationInfiniteType     of string * Type
  | RecLitUnexpectedType        of string * Type * Type
  | RecLitMissingConstructor    of Core
  | RecProjInvalidField         of string
  | RecProjInvalidRecord        of Type
  | RecDefDuplicateField        of string * Core
  | RecDefFieldAlreadyDefined   of string * Core * Type
  | ADTDefDuplicateField        of string * string
  | ADTLitMissingFields         of int * int * Core
  | ADTLitTooManyFields         of int * int * Core
  | ADTLitMissingFieldsPattern  of int * int * Pattern
  | ADTLitTooManyFieldsPattern  of int * int * Pattern
  | UnexpectedType              of Type * Type * Core
  | MatchBadPattern             of Pattern * Type
  | PatternDuplicateVar         of string * Pattern



type TypecheckResult =
  | Type      of Type
  | TypeError of TypeError



exception TypeException of TypeError



let throw (err : TypeError) = raise (TypeException err)



let throwIfConstructorDefined env s =
  let f _ =
    function
    | TADT (_, m) ->
        Map.exists (fun s2 _ -> s = s2) m

    | t -> false

  if Map.exists f (TypeEnv.ofSchemeEnv env)
    then throw (ConstructorAlreadyDefined s)
    else ()



let throwIfTypeDefined env s =
  match Map.tryFind s env with
  | Some _ -> throw (TypeAlreadyDefined s)
  | None   -> ()



let throwIfTypeUndefined env =
  let rec go =
    function
    | TUser s ->
        if Map.containsKey s env
          then ()
          else throw (UndefinedType s)

    | TFun a ->
        Array.iter go a

    | TTuple a ->
        Array.iter go a

    | TList t -> go t

    | _ -> ()

  go



let throwOrFindIfUserType env t =
  match t with
  | TUser s ->
      match SchemeEnv.tryFindType s env with
      | Some t2 -> t2
      | None    -> throw (UndefinedType s)

  | _ -> t



// ++++++++++++++++++++++
// + constraint solving +
// ++++++++++++++++++++++



let rec unifyMany ts ts2 =
  match Array.tryUncons ts, Array.tryUncons ts2 with
  | Some (t, ts3), Some (t2, ts4) ->
      let sub  = unify (Equal (t, t2))
      let sub2 =
        unifyMany
          (Array.map (Type.substitute sub) ts3)
          (Array.map (Type.substitute sub) ts4)

      Substitution.compose sub2 sub

  | None, None -> Substitution.empty

  | _ -> throw (UnificationMismatch (ts, ts2))




and unify =
  function
  | Equal (t, t2) when t = t2 -> Substitution.empty

  | Equal (TADT (s, _), t) -> unify (Equal (TUser s, t))

  | Equal (t, TADT (s, _)) -> unify (Equal (TUser s, t))

  | Equal (TRecord (s, _), t) -> unify (Equal (TUser s, t))

  | Equal (t, TRecord (s, _)) -> unify (Equal (TUser s, t))

  | Equal (TVar s, t2) when Set.contains s (Type.ftv t2) ->
      throw (UnificationInfiniteType (s, t2))

  | Equal (TVar s, t2) -> Map.singleton s t2

  | Equal (t, TVar s) -> unify (Equal (TVar s, t))

  | Equal (TFun ts, TFun ts2) -> unifyMany ts ts2

  | Equal (TTuple ts, TTuple ts2) -> unifyMany ts ts2

  | Equal (TList t, TList t2) -> unify (Equal (t, t2))

  | Equal (TRef t, TRef t2) -> unify (Equal (t, t2))

  | Equal (TArrow (t, t2), TArrow (t3, t4)) -> unifyMany [|t; t2|] [|t3; t4|]

  | OneOf (t, ts) when Array.contains t ts -> Substitution.empty

  | OneOf (t, ts) -> throw (UnificationNotOneOf (t, ts))

  | Equal (t, t2) -> throw (UnificationNotEqual (t, t2))



let solve =
  let rec go sub cs =
    match Array.tryUncons cs with
    | Some (c, cs2) ->
        let sub2 = unify c

        Array.map (Constraint.substitute sub2) cs2
        |> go (Substitution.compose sub2 sub)

    | None -> sub

  go Substitution.empty



// +++++++++++
// + Pattern +
// +++++++++++



module Pattern =
  let collectConstraintsAndSchemeEnv env t p =
    let rec goMany ts ps =
      Array.zip ts ps
      |> Array.map (uncurry go)
      |> Array.unzip
      |> Pair.mapLeft  Array.concat
      |> Pair.mapRight Array.concat

    and go t =
      function
      | PUnit     -> [|Equal (t, TUnit)  |], [||]
      | PInt _    -> [|Equal (t, TInt)   |], [||]
      | PBool _   -> [|Equal (t, TBool)  |], [||]
      | PString _ -> [|Equal (t, TString)|], [||]

      | PVar s ->
          [|Equal (t, TypeVarGen.next ())|],
          [|s, t|]

      | PList ps ->
          let t2      = TypeVarGen.next ()
          let ts      = [|for _ in ps do yield TypeVarGen.next ()|]
          let cs , xs = goMany ts ps
          let cs2     = Array.pairwiseMap (curry Equal) (Array.cons t2 ts)

          Array.concat [[|Equal (t, TList t2)|]; cs; cs2], xs

      | PListCons (p, p2) ->
          let tv       = TypeVarGen.next ()
          let cs , xs  = go tv p
          let cs2, xs2 = go t  p2

          Array.concat [[|Equal (t, (TList tv))|]; cs; cs2],
          Array.append xs xs2

      | PTuple ps ->
          let ts     = [|for _ in ps do yield TypeVarGen.next ()|]
          let cs, xs = goMany ts ps

          Array.cons (Equal (t, TTuple ts)) cs, xs

      | PADT (s, ps) ->
          match SchemeEnv.tryFindTypeOfConstructor s env with
          | None -> throw (UndefinedConstructorPattern (s, PADT (s, ps)))

          | Some (TADT (s2, m)) ->
              let ts = Array.map (throwOrFindIfUserType env) (Map.find s m)

              match Array.length ts, Array.length ps with
              | n, k when n = k ->
                  let css, xss =
                    Array.zip ts ps
                    |> Array.map (uncurry go)
                    |> Array.unzip

                  Array.cons (Equal (t, TADT (s2, m))) (Array.concat css),
                  Array.concat xss

              | n, k when k < n ->
                  throw (ADTLitMissingFieldsPattern (n, k, PADT (s, ps)))

              | n, k            ->
                  throw (ADTLitTooManyFieldsPattern (n, k, PADT (s, ps)))

          | t ->
              failwithf "Error @ Pattern.collectConstraintsAndSchemeEnv: %A" t

    let cs, kvps = go t p

    match Seq.tryFindDuplicate (Array.map fst kvps) with
    | Some s -> throw (PatternDuplicateVar (s, p))
    | None   ->
        SchemeEnv.addTypes kvps SchemeEnv.empty
        |> Pair.leftRight cs



// +++++++++
// + Param +
// +++++++++



module Param =
  let nameAndType =
    function
    | Untyped s ->
        s, TypeVarGen.next()

    | Typed (s, t) ->
        Type.unknownsToTypeVars t
        |> Type.funsToArrows
        |> Pair.leftRight s



// +++++++++++++
// + inference +
// +++++++++++++



let constraintsOfBop =
  let equal t t2 t3 t4 t5 t6 =
    [| Equal (t4, t5)
     ; Equal (t4, t)
     ; Equal (t5, t2)
     ; Equal (t6, t3)
    |]

  let oneOf ts ts2 t t4 t5 t6 =
    [| Equal (t4, t5)
     ; OneOf (t4, ts)
     ; OneOf (t5, ts2)
     ; Equal (t6, t)
    |]

  function
  | Add -> equal TInt TInt TInt
  | Sub -> equal TInt TInt TInt
  | Mul -> equal TInt TInt TInt
  | Div -> equal TInt TInt TInt

  | Eq ->
      oneOf
        [|TInt; TBool; TString|]
        [|TInt; TBool; TString|]
        TBool

  | Ne ->
      oneOf
        [|TInt; TBool; TString|]
        [|TInt; TBool; TString|]
        TBool

  | Lt -> equal TInt TInt TBool
  | Gt -> equal TInt TInt TBool
  | Le -> equal TInt TInt TBool
  | Ge -> equal TInt TInt TBool

  | Or  -> equal TBool TBool TBool
  | And -> equal TBool TBool TBool

  | ListCons -> fun t1 t2 t3 ->
      let tv = TypeVarGen.next()
      [| Equal (t1, tv)
       ; Equal (t2, TList tv)
       ; Equal (t3, TList tv)
      |]

  | ListConcat -> fun t1 t2 t3 ->
      let tv = TypeVarGen.next()
      [| Equal (t1, TList tv)
       ; Equal (t2, TList tv)
       ; Equal (t3, TList tv)
      |]

  | StringConcat -> fun t1 t2 t3 ->
      [| Equal (t1, TString)
       ; Equal (t2, TString)
       ; Equal (t3, TString)
      |]

  | RefAsn -> fun t1 t2 t3 ->
      let tv = TypeVarGen.next()
      [| Equal (t1, TRef tv)
       ; Equal (t2, tv)
       ; Equal (t3, TUnit)
      |]



let infer : SchemeEnv -> Core -> Type * Constraint [] =
  let rec goMany env =
    Array.map (go env)
    >> Array.unzip
    >> Pair.mapRight Array.concat

  and go env =
    function
    | Unit     -> TUnit  , [||]
    | Int    _ -> TInt   , [||]
    | Bool   _ -> TBool  , [||]
    | String _ -> TString, [||]

    | Var s ->
        match SchemeEnv.tryFindType s env with
        | None   -> throw (UnboundVar s)
        | Some t -> t, [||]

    | If (e1, e2, e3) ->
        let t1, cs  = go env e1
        let t2, cs2 = go env e2
        let t3, cs3 = go env e3

        t2, Array.concat [cs; cs2; cs3
                         ; [| Equal (t1, TBool); Equal (t2, t3)|]
                         ]

    | Abs (p, e) ->
        let s , t  = Param.nameAndType p
        let t2, cs = go (SchemeEnv.addType s t env) e
        TArrow (t, t2), cs

    | Bop (e, op, e2) ->
        let t , cs  = go env e
        let t2, cs2 = go env e2
        let tv      = TypeVarGen.next()

        tv, Array.concat [cs; cs2; constraintsOfBop op t t2 tv]

    | Fix e ->
        let t , cs = go env e
        let tv     = TypeVarGen.next ()
        tv, Array.cons (Equal (TArrow (tv, tv), t)) cs

    | App (e, e2) ->
        let t , cs  = go env e
        let t2, cs2 = go env e2
        let tv      = TypeVarGen.next()

        tv, Array.concat [cs; cs2; [|Equal (t, TArrow (t2, tv))|]]

    | Let (s, t, e, e2) ->
        let t2, cs  = go env e

        let sub     = solve cs

        let env2    = SchemeEnv.substitute sub env
        let scheme  = SchemeEnv.generalize (Type.substitute sub t2) env2
        let t3, cs2 = go (Map.add s scheme env2) e2

        let t4 =
          Type.unknownsToTypeVars t
          |> Type.funsToArrows

        t3, Array.concat [cs; cs2; [|Equal (t4, t3)|]]

    | TopLet (s, t, e) -> go env (Let (s, t, e, (Var s)))

    | List es ->
        let tv      = TypeVarGen.next ()
        let ts, cs  = goMany env es
        let     cs2 = Array.pairwiseMap (curry Equal) (Array.cons tv ts)

        TList tv, Array.append cs cs2

    | Core.Seq es -> Pair.mapLeft Array.last (goMany env es)

    | RefLit e -> Pair.mapLeft TRef (go env e)

    | DeRef e ->
        let tv    = TypeVarGen.next ()
        let t, cs = go env e
        tv, Array.cons (Equal (t, TRef tv))  cs

    | Tuple es -> Pair.mapLeft TTuple (goMany env es)

    | DefRecord (s, xs) ->
        throwIfTypeDefined env s

        let f s2 =
          Option.map
            (Pair.leftRight s2)
            (SchemeEnv.tryFindTypeWithField s2 env)

        match Array.tryPick f (Array.map fst xs) with
        | Some (s2, t) ->
            throw (RecDefFieldAlreadyDefined (s2, DefRecord (s, xs), t))

        | None ->
            match Seq.tryFindDuplicate (Array.map fst xs) with
            | None    -> TRecord(s, Map.ofSeq xs), [||]
            | Some s2 -> throw (RecDefDuplicateField(s2, DefRecord (s, xs)))

    | Record ("", xs) -> throw (RecLitMissingConstructor (Record ("", xs)))
    | Record (s , xs) ->
        match SchemeEnv.tryFindType s env with
        | None -> throw (UndefinedType s)

        | Some (TRecord (_, m)) ->
            let ys             = Array.sortBy fst xs
            let ys2            = Array.sortBy fst (Map.toArray m)
            let fields1        = Array.map fst ys
            let fields2        = Array.map fst ys2
            let missingField   = Seq.tryFindMissing   fields2 fields1
            let invalidField   = Seq.tryFindMissing   fields1 fields2
            let duplicateField = Seq.tryFindDuplicate fields1

            match missingField, invalidField, duplicateField with
            | Some s2, _      , _       -> throw (RecLitMissingField s2)
            | _      , Some s2, _       -> throw (RecLitInvalidField s2)
            | _      , _      , Some s2 -> throw (RecLitDuplicateField s2)
            | None   , None   , None    ->
                let ts , cs = goMany env (Array.map snd ys)
                let ts2     = Array.map snd ys2

                TUser s, Array.append (Array.map2 (curry Equal) ts ts2) cs

        | Some t ->
            throw
              (UnexpectedType (t, TRecord (s, Map.empty), Record (s, xs)))

    | ProjRec(e, s) ->
        match SchemeEnv.tryFindTypeWithField s env with
        | None -> throw (RecProjInvalidField s)
        | Some (TRecord (_, m) as t) ->
            let t2, cs = go env e

            Map.find s m, Array.cons (Equal (t, t2)) cs

        | x -> failwithf "Error3 @ infer %A" x

    | DefADT (s, xs) ->
        throwIfTypeDefined env s

        let ss, ts = Array.unzip xs

        match Seq.tryFindDuplicate ss with
        | Some s2 -> throw (ADTDefDuplicateField (s, s2))
        | None    ->
            Array.iter (throwIfConstructorDefined env) ss

            let validateTypes =
              function
              | TUser s3 when s = s3 -> ()
              | t -> throwIfTypeUndefined env t

            Array.iter validateTypes (Array.concat ts)

            TADT (s, Map.ofSeq xs), [||]

    | ADT (s, es) ->
        match SchemeEnv.tryFindTypeOfConstructor s env with
        | Some (TADT (s2, m)) ->
            let ts = Array.map (throwOrFindIfUserType env) (Map.find s m)

            match Array.length ts, Array.length es with
            | n, k when n = k ->
                let ts2, cs = goMany env es
                TUser s2, Array.append (Array.map2 (curry Equal) ts ts2) cs

            | n, k when k < n -> throw (ADTLitMissingFields (n, k, ADT (s, es)))
            | n, k            -> throw (ADTLitTooManyFields (n, k, ADT (s, es)))

        | None -> throw (UndefinedConstructor (s, ADT (s, es)))

        | t -> failwithf "Error2 @ typeOfExpr: %A" t

    | Match (e, xs) ->
        let ps, es = Array.unzip xs
        let t , cs = go env e

        let css, envs =
          Array.map (Pattern.collectConstraintsAndSchemeEnv env t) ps
          |> Array.unzip

        let ts, css2 =
          Array.zip envs es
          |> Array.map (fun (env2, e) -> go (Map.union env2 env) e)
          |> Array.unzip

        let tv = TypeVarGen.next ()

        tv, Array.concat
              [ cs
              ; Array.concat css
              ; Array.concat css2
              ; Array.pairwiseMap (curry Equal) (Array.cons tv ts)
              ]

    | t -> failwithf "Error @ infer: %A" t

  go



// +++++++++++++
// + interface +
// +++++++++++++



module Core =
  let typeOf (env : TypeEnv) (e : Core) =
    let go () =
      TypeVarGen.reset () // global mutable state :(

      let env2 =
        Map.mapValues Type.funsToArrows env
        |> SchemeEnv.ofTypeEnv

      let t, cs = infer env2 e
      let sub   = solve cs

      TypeVarGen.reset () // global mutable state :(

      Type.substitute sub t
      |> throwOrFindIfUserType env2
      |> Type.arrowsToFuns
      |> Type.canonicalize

    try
      Type (go ())
    with
      | TypeException err -> TypeError err



// ++++++++
// + test +
// ++++++++



let tp env s =
  let go e =
    match Core.typeOf env (Core.ofExpr e) with
    | TypeError err -> printfn "%A" err; TUnit
    | Type t -> Type.prettyPrint t; t

  match parse s with
  | AST (Prgm es) -> go es.[0]
  | AST (Expr e)  -> go e

  | AST Empty -> failwith "{}"; TUnit
  | Error s   -> failwithf "%s" s; TUnit



let test () =
  // let t    = tp Map.empty "let id x = x"
  // let env  = Map.singleton "id" t
  // let t2   = tp env "let f g x (y : Bool) = id (g x) = y"
  // let env2 = Map.add "f" t2 env
  // let t3   = tp env2 "type A = {b : Int, c : Bool}"
  // let env3 = Map.add "A" t3 env2
  // let t4   = tp env3 "id (A {b = id 1337, c = True && False}).b"
  // let t5   = tp env3 "type L = C : (Int, L) | E"
  // let env4 = Map.add "L" t5 env3
  // let t6   = tp env4 "C (1300, C (37, E))"
  // let env5 = Map.add "x" t6 env4
  // let t7   = tp env5 "let flip f x y = f y x"
  // let t8   = tp env5 "match (x) {C (y, _) -> y | E -> 0}"
  // let t9   = tp env5 "match (x) {C (y, z) -> z | E -> E}"
  // let t10  = tp env5 "let rec g x = match (x) {y :: ys -> 1 + g ys | [] -> 0}"
  // let t11  = tp env5 "let rec g x = match (x) {[x, y, z] -> x + y + z}"
  // let env6 = Map.add "g" t10 env5
  let t12  = tp Map.empty "[1, 2, 3]" //" 2 :: 3 :: [])"
  // let t13  = tp Map.empty "let rec fold f acc xs = \
  //                             match (xs) { \
  //                             | [] -> acc \
  //                             | x :: xs -> fold f (f acc x) xs \
  //                             }"
  ()
