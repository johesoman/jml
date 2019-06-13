module Eval


open Log
open Lang
open Type
open Pretty
open Parser
open Extensions
open Combinators



// +++++++++
// + State +
// +++++++++



type Env = (string * Type * Core) []

type TypeEnv = Map<string, Type>

type Store = Core []

type State =
  { topEnv   : Env
  ; refStore : Store
  }

type WhatToPrint =
  | Nothing
  | AllSteps
  | JustResult



module State =
  let empty : State =
    { topEnv   = [||]
    ; refStore = [||]
    }



  let tryFindIndexOfTop (s : string) (st : State) =
    Array.tryFindIndexBack (fun (s2, _, _) -> s = s2) st.topEnv



  let storeAlloc (x : Core) (st : State) =
    Array.length st.refStore,
    {st with refStore = Array.snoc st.refStore x}



  let storeFetch (i : int) (st : State) = st.refStore.[i]



  let storeUpdate (i : int) (x : Core) (st : State) =
    {st with refStore = Array.update i x st.refStore}



  let typeEnv (st : State) =
    Array.fold (fun m (s, t, _) -> Map.add s t m) Map.empty st.topEnv



  let topEnvAdd s (t, e) (st : State) =
    {st with topEnv = Array.snoc st.topEnv (s, t, e)}



  let topEnvGetExpr (i : int) (st : State) =
    let _, _, e = st.topEnv.[i]
    e



// ++++++++++++++++
// + substitution +
// ++++++++++++++++



module Pattern =
  let rec collectVars =
    function
    | PUnit       -> [||]
    | PInt _      -> [||]
    | PBool _     -> [||]
    | PString _   -> [||]
    | PList [||]  -> [||]
    | PVar s      -> [|s|]
    | PList ps    -> Array.collect collectVars ps
    | PTuple ps   -> Array.collect collectVars ps
    | PADT(_, ps) -> Array.collect collectVars ps

    | PListCons (p, p2) ->
        Array.append (collectVars p) (collectVars p2)




module Core =
  let isConstant =
    function
    | Unit        -> true
    | Int _       -> true
    | Bool _      -> true
    | String _    -> true
    | _           -> false



  let rec isValue =
    function
    | e when isConstant e -> true

    | Ref _ -> true
    | Abs _ -> true

    | Tuple es -> Array.forall isValue es

    | List es -> Array.forall isValue es

    | Record (_, xs) ->
        Array.map snd xs
        |> Array.forall isValue

    | ADT (_, es) -> Array.forall isValue es

    | _ -> false



  let map onIdx =
    let rec go c =
      function
      | Fix e -> Fix(go c e)

      | e when isConstant e -> e

      | RefLit e -> RefLit (go c e)
      | DeRef  e -> DeRef  (go c e)

      | Record (s, xs) ->
          Record(s, Array.map (Pair.mapRight (go c)) xs)

      | Match (e1, xs) ->
          let f (p, e2) =
            let n = Array.length (Pattern.collectVars p)
            p, go (c + n) e2

          Match (go c e1, Array.map f xs)

      | Index(s, i)       -> onIdx c s i

      | TopIndex (s, i)   -> TopIndex (s, i)

      | ProjRec(e, s)     -> ProjRec(go c e, s)

      | Abs(p, e)         -> Abs(p, go (c + 1) e)

      | App(e1, e2)       -> App(go c e1, go c e2)

      | Seq es            -> Seq (Array.map (go c) es)

      | Bop(e1, op, e2)   -> Bop (go c e1, op, go c e2)

      | List es           -> List (Array.map (go c) es)

      | Tuple es          -> Tuple (Array.map (go c) es)

      | ADT (s, es)       -> ADT (s, Array.map (go c) es)

      | If(e1, e2, e3)    -> If(go c e1, go c e2, go c e3)

      | Let(s, t, e1, e2) -> Let(s, t, go c e1, go (c + 1) e2)

      | e -> failwithf "Error @ Core.map: %A" e

    go 0



  let shift d =
    let onIdx c s i =
      if c <= i
        then Index(s, i + d)
        else Index(s, i)

    map onIdx



  let substitute e1 e2 =
    let onIdx c s i =
      if c = i
        then shift (c + 1) e1
        else Index(s, i)

    map onIdx e2
    |> shift (-1)



  let convertToDeBrujinIndexing (st : State) : Core -> Core =
    let rec go ss =
      function
      | Var s ->
          match List.tryFindIndex ((=) s) ss with
          | Some i -> Index (s, i)
          | None   ->
              match State.tryFindIndexOfTop s st with
              | Some i -> TopIndex (s, i)
              | None   -> failwith "Error @ toNameless: None"

      | e when isConstant e -> e

      | Fix e                 -> Fix(go ss e)

      | RefLit e              -> RefLit (go ss e)

      | DeRef  e              -> DeRef  (go ss e)

      | ProjRec(e, s)         -> ProjRec (go ss e, s)

      | App (e1, e2)          -> App (go ss e1, go ss e2)

      | Seq es                -> Seq (Array.map (go ss) es)

      | List es               -> List (Array.map (go ss) es)

      | Tuple es              -> Tuple (Array.map (go ss) es)

      | Bop (e1, op, e2)      -> Bop (go ss e1, op, go ss e2)

      | ADT (s, es)           -> ADT (s, Array.map (go ss) es)

      | Abs (Untyped s, e)    -> Abs (Untyped s, go (s :: ss) e)

      | Abs (Typed (s, t), e) -> Abs (Typed (s, t), go (s :: ss) e)

      | If  (e1, e2, e3)      -> If  (go ss e1, go ss e2, go ss e3)

      | Let (s, t, e1, e2)    -> Let (s, t, go ss e1, go (s :: ss) e2)

      | Match (e1, xs) ->
          let f (p, e2) =
            p, go ((Array.toList (Pattern.collectVars p)) @ ss) e2

          Match (go ss e1, Array.map f xs)

      | Record (s, es) -> Record(s, Array.map (Pair.mapRight (go ss)) es)

      | e -> failwithf "Error @ toNameless: %A" e

    go []



// ++++++++++++++
// + evaluation +
// ++++++++++++++



exception NoRuleApplies of Core * State



let evalPattern (e1 : Core) (p : Pattern) (e2 : Core) : Core option =
  let rec go p e3 =
    match p, e3 with
    | PInt    x, Int y    when x = y -> Some [||]
    | PBool   x, Bool y   when x = y -> Some [||]
    | PString x, String y when x = y -> Some [||]
    | PUnit    , Unit                -> Some [||]
    | PVar    _, _                   -> Some [|e3|]

    | PListCons (p, p2), List es ->
        match Array.tryUncons es with
        | None         -> None
        | Some (e, es2) ->
            Array.collectArrayOption (uncurry go) [|p, e; p2, List es2|]

    | PList ps, List es ->
        Array.collectArrayOption (uncurry go) (Array.zip ps es)

    | PTuple ps, Tuple es ->
        Array.collectArrayOption (uncurry go) (Array.zip ps es)

    | PADT (s1, ps), ADT (s2, es) when s1 = s2 ->
        Array.collectArrayOption (uncurry go) (Array.zip ps es)

    | _ -> None

  Option.map (Array.fold (flip Core.substitute) e2) (go p e1)



let rec evalBop (st : State) =
  function
  | Bop(e, op, e2) when Core.isValue e && Core.isValue e2 ->
      match e, op, e2 with
      // Int -> Int -> Int
      | Int x, Add, Int y -> x +  y |> Int, st
      | Int x, Sub, Int y -> x -  y |> Int, st
      | Int x, Mul, Int y -> x *  y |> Int, st
      | Int x, Div, Int y -> x /  y |> Int, st

      // Int -> Int -> Bool
      | Int x, Eq , Int y -> x =  y |> Bool, st
      | Int x, Ne , Int y -> x <> y |> Bool, st
      | Int x, Lt , Int y -> x <  y |> Bool, st
      | Int x, Le , Int y -> x <= y |> Bool, st
      | Int x, Gt , Int y -> x >  y |> Bool, st
      | Int x, Ge , Int y -> x >= y |> Bool, st

      // Bool -> Bool -> Bool
      | Bool x, Or , Bool y -> (x || y) |> Bool, st
      | Bool x, And, Bool y -> (x && y) |> Bool, st
      | Bool x, Eq , Bool y ->  x =  y  |> Bool, st
      | Bool x, Ne , Bool y ->  x <> y  |> Bool, st

      // the rest
      | Ref i, RefAsn, x -> Unit, State.storeUpdate i x st

      | String x, StringConcat, String y -> x + y |> Core.String, st

      | List [||], ListConcat, e         -> e, st
      | e        , ListConcat, List [||] -> e, st
      | List es  , ListConcat, List es2  -> List (Array.append es es2), st

      | e, ListCons, List es -> List (Array.cons e es), st

      | _ -> failwithf "Error3 @ evalBop: %A" (Bop (e, op, e2))

  | Bop (v, op, e1) when Core.isValue v  ->
      let e2, st2 = evalCore1 st e1
      Bop (v , op, e2), st2

  | Bop (e1, op, e2) ->
      let e3, st2 = evalCore1 st e1
      Bop (e3, op, e2), st2

  | e -> failwithf "Error1 @ evalBop: %A" e



and tryEvalNext (st : State) (es : Core []) =
  match Array.tryFindIndex (Core.isValue >> not) es with
  | None   -> None
  | Some i ->
      let e, st2 = evalCore1 st es.[i]
      Some (Array.update i e es, st2)



and evalCore1 (st : State) =
  function
  | e when Core.isValue e ->
      raise (NoRuleApplies (e, st))

  | TopIndex (_, i) ->
      State.topEnvGetExpr i st, st

  | Bop _ as e ->
      evalBop st e

  | RefLit e when Core.isValue e ->
      Pair.mapLeft Ref (State.storeAlloc e st)

  | RefLit e ->
      Pair.mapLeft RefLit (evalCore1 st e)

  | DeRef (Ref i) ->
      State.storeFetch i st, st

  | DeRef e ->
      Pair.mapLeft DeRef (evalCore1 st e)

  | Fix (Abs(_, e)) as e2 ->
      Core.substitute e2 e, st

  | App(Abs(_,e), e2) when Core.isValue e2 ->
      Core.substitute e2 e, st

  | App (e, e2) when Core.isValue e ->
      Pair.mapLeft (Pair.leftRight e >> App) (evalCore1 st e2)

  | App (e, e2) ->
      Pair.mapLeft (Pair.rightLeft e2 >> App) (evalCore1 st e)

  | Let (_, _, e, e2) when Core.isValue e ->
      Core.substitute e e2, st

  | Let (s, t, e1, e2) ->
      let e3, st2 = evalCore1 st e1
      Let(s, t, e3, e2), st2

  | If (Bool true , e2, _) -> e2, st
  | If (Bool false, _, e3) -> e3, st

  | If (e1, e2, e3) ->
      let e4, st2 = evalCore1 st e1
      If(e4, e2, e3), st2

  | Record (s, xs) ->
      let ss, es = Array.unzip xs
      match tryEvalNext st es with
      | None -> Record (s, xs), st
      | Some (es2, st2) -> Record (s, Array.zip ss es2), st2

  | ProjRec (e, s) when not (Core.isValue e) ->
      Pair.mapLeft (Pair.rightLeft s >> ProjRec) (evalCore1 st e)

  | ProjRec (Record(_, xs), s) ->
      Map.find s (Map.ofArray xs), st

  | Seq es ->
      match tryEvalNext st es with
      | None -> Array.last es, st
      | Some (es2, st2) -> Seq es2, st2

  | Tuple es ->
      match tryEvalNext st es with
      | None -> Tuple es, st
      | Some (es2, st2) -> Tuple es2, st2

  | List es ->
      match tryEvalNext st es with
      | None -> List es, st
      | Some (es2, st2) -> List es2, st2

  | Match (e, xs) when Core.isValue e ->
      match Array.tryPick (uncurry (evalPattern e)) xs with
      | Some e2 -> e2, st
      | None    -> raise (NoRuleApplies (Match (e, xs), st))

  | Match (e, xs) ->
      Pair.mapLeft (Pair.rightLeft xs >> Match) (evalCore1 st e)

  | e -> raise (NoRuleApplies (e, st))



and evalToValue st1 =
  function
  | e when Core.isValue e -> e, st1
  | e ->
      let e2, st2 = evalCore1 st1 e
      evalToValue st2 e2



let printFirst = Core.prettyPrint



let printNext =
      Core.prettyString
   >> String.toLines
   >> Seq.toArray
   >> (function
       | [||] -> printfn "{}"
       | xs   ->
           printfn "  => %s" xs.[0]
           for x in xs.[1..] do
             printfn "     %s" x)



let evalCore (whatToPrint : WhatToPrint) =
  let rec go isFirst (st : State) (e : Core) =
    let maybePrintStep _ =
      match whatToPrint, isFirst with
      | AllSteps, true  -> printFirst e
      | AllSteps, false -> printNext  e
      | _ -> ()

    maybePrintStep()

    try
      let e2, st2 = evalCore1 st e
      go false st2 e2
    with
      | NoRuleApplies (e2, st2) -> e2, st2

  go true



let evalTop (whatToPrint : WhatToPrint) (st : State) =
  function
  | TopLet (s, _, e) as e2 -> // not checking type atm
      match Core.typeOf (Map.remove s (State.typeEnv st)) e2 with
      | Type t2 ->
          let e3      = Core.convertToDeBrujinIndexing st e
          let e4, st2 = evalCore whatToPrint st e3

          if whatToPrint = Nothing
            then ()
            else printfn "\nval %s : %s" s (Type.prettyString t2)

          State.topEnvAdd s (t2, e4) st2

      | TypeError err -> printfn "%A" err; st

  | DefADT _ as e ->
      match Core.typeOf (State.typeEnv st) e with
      | TypeError err -> printfn "%A" err; st

      | Type (TADT (s, _) as t) ->
          if whatToPrint = Nothing
            then ()
            else printfn "\n%s" (Core.prettyString e)

          State.topEnvAdd s (t, Unit) st

      | t -> failwithf "Error @ evalTop: %A" t

  | DefRecord _ as e ->
      match Core.typeOf (State.typeEnv st) e with
      | TypeError err -> printfn "%A" err; st

      | Type (TRecord (s, _) as t) ->
          if whatToPrint = Nothing
            then ()
            else printfn "\n%s" (Core.prettyString e)

          State.topEnvAdd s (t, Unit) st

      | t -> failwithf "Error2 @ evalTop: %A" t

    | t -> failwithf "Error3 @ evalTop: %A" t



let evalPrgm (whatToPrint : WhatToPrint) (st : State) =
  Array.map Core.ofExpr
  >> Array.fold (evalTop whatToPrint) st



// +++++++++++++
// + interface +
// +++++++++++++



module AST =
  let eval (whatToPrint : WhatToPrint) (st : State) (ast : AST) =
    match ast with
    | Prgm es -> evalPrgm whatToPrint st es
    | Expr e  ->
        let e2 = Core.ofExpr e
        match Core.typeOf (State.typeEnv st) e2 with
        | Type t ->
            let e3      = Core.convertToDeBrujinIndexing st e2
            let e4, st2 = evalCore whatToPrint st e3

            let ss = Core.prettyString e4 |> String.toLines

            match whatToPrint, Array.length ss with
            | Nothing, _ -> ()
            | _, n when n < 2 ->
                printfn "\nval it : %s = %s"
                  (Type.prettyString t)
                  (String.fromLines ss)

            | _, _ ->
                printfn "\nval it : %s =" (Type.prettyString t)
                Array.iter (printfn "  %s") ss

            State.topEnvAdd "it" (t, e4) st2

        | TypeError err ->
            printfn "%A" err;
            st

    | Empty -> st



// ++++++++
// + test +
// ++++++++



let init = State.empty



let eval whatToPrint s st =
  match parse s with
  | AST ast   -> logp ast |> AST.eval whatToPrint st
  | Error err -> printfn "%s" err; st



let wait x =
  printfn "waiting...";
  ignore (System.Console.ReadLine())
  x



let stop = ignore



let test1 () =
  init

  |> eval Nothing  "type L = C : (Int, L) | E"

  |> eval Nothing  "let rec f (xs : L) : Int = \
                      match (xs) {\
                      | E -> 0
                      | C (x, ys) -> x + f ys
                      }"

  |> eval AllSteps "f (C (1000, C (300, C (30, C (7, E))))))"

  |> stop



let test2 () =
  init

  |> eval AllSteps "let x : &Int = &1300"
  |> eval AllSteps "!x"
  |> eval AllSteps "x := !x + 37"
  |> eval AllSteps "!x"

  |> stop


let test3 () =
  init

  |> eval AllSteps "1 :: 2 :: []"

  |> stop
