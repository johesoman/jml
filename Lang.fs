module Lang



open Extensions
open Combinators



type Type =
  | TAny
  | TUnit
  | TInt
  | TBool
  | TString
  | TUnknown
  | TRef        of Type
  | TList       of Type
  | TUser       of string
  | TFun        of Type []
  | TTuple      of Type []
  | TArrow      of Type * Type
  | TRecord     of string * Map<string, Type>
  | TADT        of string * Map<string, Type []>
  | TVar        of string



type Param =
  | Untyped of string
  | Typed   of string * Type



module Param =
  let name =
    function
    | Untyped s    -> s
    | Typed (s, _) -> s



module Type =
  let flattenUnknowns t =
    let rec go =
      function
      | TFun   ts -> Array.exists go ts
      | TTuple ts -> Array.exists go ts
      | TList  t  -> go t
      | TRef   t  -> go t

      | TArrow (t, t2) -> go t || go t2

      | TUnknown -> true

      | _ -> false

    if go t
      then TUnknown
      else t


  let ofParam =
    function
    | Untyped s   -> TUnknown
    | Typed(s, t) -> t



  let rec funsToArrows =
    function
    | TFun ts ->
        Array.map funsToArrows ts
        |> Array.reduceBack (curry TArrow)

    | TTuple ts -> TTuple (Array.map funsToArrows ts)

    | TRef  t -> TRef  (funsToArrows t)
    | TList t -> TList (funsToArrows t)

    | TADT (s, m) -> TADT (s, Map.mapValues (Array.map funsToArrows) m)

    | TRecord (s, m) -> TRecord (s, Map.mapValues funsToArrows m)

    | t -> t



  let rec arrowsToFuns =
    function
    | TArrow (t, t2) ->
        match arrowsToFuns t2 with
        | TFun ts -> TFun (Array.cons (arrowsToFuns t) ts)
        | t3      -> TFun [|arrowsToFuns t; t3|]

    | TTuple ts -> TTuple (Array.map arrowsToFuns ts)

    | TRef  t -> TRef  (arrowsToFuns t)
    | TList t -> TList (arrowsToFuns t)

    | TADT (s, m) -> TADT (s, Map.mapValues (Array.map arrowsToFuns) m)

    | TRecord (s, m) -> TRecord (s, Map.mapValues arrowsToFuns m)

    | t -> t



type Op =
  | Add
  | Sub
  | Mul
  | Div
  | Eq
  | Ne
  | Lt
  | Gt
  | Le
  | Ge
  | Or
  | And
  | RefAsn
  | ListCons
  | ListConcat
  | StringConcat



type Pattern =
  | PUnit
  | PList        of Pattern []
  | PInt         of int
  | PBool        of bool
  | PVar         of string
  | PString      of string
  | PTuple       of Pattern []
  | PListCons    of Pattern * Pattern
  | PADT         of string * Pattern []



type Core =
  | Unit
  | Int         of int
  | Bool        of bool
  | Fix         of Core
  | Var         of string
  | String      of string
  | Ref         of int
  | DeRef       of Core
  | RefLit      of Core
  | App         of Core * Core
  | Abs         of Param * Core
  | ProjAgg     of Core * Core
  | ProjRec     of Core * string
  | Bop         of Core * Op * Core
  | Record      of string * (string * Core) []
  | Match       of Core * (Pattern * Core) []
  | List        of Core []
  | ADT         of string * Core []
  | DefADT      of string * (string * Type []) []
  | DefRecord   of string * (string * Type) []
  | Tuple       of Core []
  | Seq         of Core []
  | Index       of string * int
  | TopIndex    of string * int
  | If          of Core * Core * Core
  | TopLet      of string * Type * Core
  | Let         of string * Type * Core * Core



type Expr =
  | EUnit
  | EList              of Expr []
  | EFix               of Expr
  | EInt               of int
  | EBool              of bool
  | EVar               of string
  | EString            of string
  | EApp               of Expr * Expr
  | ESeq               of Expr []
  | EBop               of Expr * Op * Expr
  | ELambda            of Param [] * Expr
  | EIf                of Expr * Expr * Expr
  | EMatch             of Expr * (Pattern * Expr) []
  | ERef               of int
  | EDeRef             of Expr
  | ERefLit            of Expr
  | EProjAgg           of Expr * Expr
  | EProjRec           of Expr * string
  | EConstructor       of string
  | ERecordLit         of (string * Expr) []
  | EDefADT            of string * (string * Type []) []
  | EDefRecord         of string * (string * Type) []
  | ETuple             of Expr []
  | ETopLet            of string * Param [] * Type * Expr
  | ETopLetRec         of string * Param [] * Type * Expr
  | ELet               of string * Param [] * Type * Expr * Expr
  | ELetRec            of string * Param [] * Type * Expr * Expr



type AST =
  | Prgm of Expr []
  | Expr of Expr
  | Empty



module Expr =
  let precedence =
    function
    | EDefADT _                 -> 0
    | EDefRecord _              -> 0
    | ELet _                    -> 1
    | ELetRec _                 -> 1
    | ETopLet _                 -> 1
    | ETopLetRec _              -> 1
    | ELambda _                 -> 1
    | EIf _                     -> 1
    | EMatch _                  -> 1
    | ESeq _                    -> 2
    | EBop (_, RefAsn, _)       -> 3
    | EBop (_, Or , _)          -> 4
    | EBop (_, And, _)          -> 5
    | EBop (_, Eq , _)          -> 6
    | EBop (_, Ne , _)          -> 6
    | EBop (_, Lt , _)          -> 6
    | EBop (_, Gt , _)          -> 6
    | EBop (_, Le , _)          -> 6
    | EBop (_, Ge , _)          -> 6
    | EBop (_, ListConcat, _)   -> 7
    | EBop (_, StringConcat, _) -> 7
    | EBop (_, ListCons, _)     -> 8
    | EBop (_, Add, _)          -> 9
    | EBop (_, Sub, _)          -> 9
    | EBop (_, Mul, _)          -> 10
    | EBop (_, Div, _)          -> 10
    | EApp _                    -> 11
    | EConstructor _            -> 11
    | EDeRef _                  -> 11
    | ERefLit _                 -> 11
    | EProjRec _                -> 12
    | EProjAgg _                -> 12
    | EFix _                    -> 13
    | EVar _                    -> 13
    | EInt _                    -> 13
    | EBool _                   -> 13
    | EString _                 -> 13
    | ERecordLit _              -> 13
    | EList _                   -> 13
    | ERef _                    -> 13
    | ETuple _                  -> 13
    | EUnit                     -> 13



  let rec ofCore =
    function
    | Unit     -> EUnit
    | Int    x -> EInt x
    | Var    s -> EVar s
    | Bool   x -> EBool x
    | String s -> EString s

    | Index    (s, _) -> EVar s
    | TopIndex (s, _) -> EVar s

    | Ref i    -> ERef i
    | DeRef  e -> EDeRef  (ofCore e)
    | RefLit e -> ERefLit (ofCore e)

    | Bop (e1, op, e2) -> EBop(ofCore e1, op, ofCore e2)

    | DefADT (s, xs)  -> EDefADT (s, xs)

    | Match (e1, es) -> EMatch (ofCore e1, Array.map (Pair.mapRight ofCore) es)

    | App (e1, e2) -> EApp(ofCore e1, ofCore e2)

    | Abs (p, e1) ->
        match ofCore e1 with
        | ELambda(ps, e2) -> ELambda(Array.append [|p|] ps, e2)
        | e2              -> ELambda([|p|], e2)

    | Let (s, t, e1, e2) ->
        match (ofCore e1, ofCore e2) with
        | ELambda(ps, e3), e4 -> ELet(s, ps, t, e3, e4)
        | e3             , e4 -> ELet(s, [||], t, e3, e4)

    | TopLet (s, t, e1) ->
        match ofCore e1 with
        | ELambda(ps, e2) -> ETopLet(s, ps, t, e2)
        | e2              -> ETopLet(s, [||], t, e2)

    | If (e1, e2, e3) -> EIf (ofCore e1, ofCore e2, ofCore e3)

    | Fix e -> EFix (ofCore e)

    | Tuple a -> ETuple (Array.map ofCore a)

    | Record (s, xs) ->
        Array.map (Pair.mapRight ofCore) xs
        |> ERecordLit
        |> Pair.leftRight (EConstructor s)
        |> EApp

    | ProjRec (e, s) -> EProjRec(ofCore e, s)

    | List es   -> EList (Array.map ofCore es)

    | Core.Seq a -> ESeq (Array.map ofCore a)

    | DefRecord (s, a) -> EDefRecord(s, a)

    | ProjAgg (e, e2) -> EProjAgg (ofCore e, ofCore e2)

    | ADT (s, [| |]) -> EConstructor s
    | ADT (s, [|e|]) -> EApp (EConstructor s, ofCore e)
    | ADT (s, es)    -> EApp (EConstructor s, ETuple (Array.map ofCore es))



  let rec ofPattern =
    function
    | PUnit     -> EUnit
    | PVar s    -> EVar s
    | PInt x    -> EInt x
    | PBool x   -> EBool x
    | PString s -> EString s


    | PList ps -> EList (Array.map ofPattern ps)

    | PTuple ps -> ETuple (Array.map ofPattern ps)

    | PListCons (p, p2) -> EBop (ofPattern p, ListCons, ofPattern p2)

    | PADT (s, [| |]) -> EConstructor s
    | PADT (s, [|p|]) -> EApp (EConstructor s, ofPattern p)
    | PADT (s, ps)    -> EApp (EConstructor s, ETuple (Array.map ofPattern ps))



module Core =
  let rec ofExpr =
    function
    | EUnit      -> Unit
    | EInt x     -> Int x
    | EVar s     -> Var s
    | EBool x    -> Bool x
    | EString s  -> String s

    | ERef i    -> Ref i
    | EDeRef  e -> DeRef  (ofExpr e)
    | ERefLit e -> RefLit (ofExpr e)

    | EBop (e1, op, e2) -> Bop (ofExpr e1, op, ofExpr e2)

    | EDefADT (s, xs) -> DefADT (s, xs)

    | EMatch (e1, es) -> Match (ofExpr e1, Array.map (Pair.mapRight ofExpr) es)

    | EApp (EConstructor s, ERecordLit xs) ->
        Array.map (Pair.mapRight ofExpr) xs
        |> Pair.leftRight s
        |> Record

    | ERecordLit xs ->
        Array.map (Pair.mapRight ofExpr) xs
        |> Pair.leftRight ""
        |> Record

    | EApp (EConstructor s, ETuple es) ->
        Array.map ofExpr es
        |> Pair.leftRight s
        |> ADT

    | EApp (EConstructor s, e) -> ADT (s, [|ofExpr e|])

    | EConstructor s -> ADT (s, [||])

    | EApp (e1, e2) -> App (ofExpr e1, ofExpr e2)

    | ELambda (ps, e) -> Array.foldBack (curry Abs) ps (ofExpr e)

    | ELet (s1, ps1, t1, e1, e2) ->
        match ofExpr (ETopLet(s1, ps1, t1, e1)) with
        | TopLet (s2, t2, e3) ->
            Let (s2, t2, e3, ofExpr e2)

        | e -> failwithf "Error2 @ Core.ofExpr: %A" e

    | ELetRec (s1, ps1, t1, e1, e2) ->
        match ofExpr (ETopLetRec(s1, ps1, t1, e1)) with
        | TopLet (s2, t2, e3) ->
            Let (s2, t2, e3, ofExpr e2)

        | e -> failwithf "Error3@ Core.ofExpr: %A" e

    | ETopLet (s, [||], t1, e) -> TopLet(s, t1, ofExpr e)

    | ETopLet (s, ps, t1, e) ->
        let t2 = TFun (Array.append (Array.map Type.ofParam ps) [|t1|])
        TopLet (s, t2, ofExpr (ELambda(ps, e)))

    | ETopLetRec (s1, ps, t1, e1) ->
        let t2 =
          match ps with
          | [||] -> t1
          | _    -> TFun (Array.append (Array.map Type.ofParam ps) [|t1|])

        let p =
          match t2 with
          | TUnknown -> Untyped s1
          | _        -> Typed (s1, t2)

        let e2 = ofExpr (ELambda(ps, e1))

        TopLet (s1, t2, Fix (Abs(p, e2)))

    | EIf (e1, e2, e3) -> If (ofExpr e1, ofExpr e2, ofExpr e3)

    | ETuple a -> Tuple (Array.map ofExpr a)

    | ESeq a -> Core.Seq (Array.map ofExpr a)

    | EList es   -> List (Array.map ofExpr es)

    | EDefRecord (s, a) -> DefRecord (s, a)

    | EProjRec (e, s) -> ProjRec (ofExpr e, s)

    | EFix e -> Fix (ofExpr e)

    | EProjAgg (e, e2) -> ProjAgg (ofExpr e, ofExpr e2)



  let rec ofPattern =
    function
    | PUnit     -> Unit
    | PVar s    -> Var s
    | PInt x    -> Int x
    | PBool x   -> Bool x
    | PString s -> String s
    | PTuple ps -> Tuple (Array.map ofPattern ps)

    | PList ps -> List (Array.map ofPattern ps)

    | PListCons (p, p2) -> Bop (ofPattern p, ListCons, ofPattern p2)

    | PADT (s, ps) -> ADT (s, Array.map ofPattern ps)


