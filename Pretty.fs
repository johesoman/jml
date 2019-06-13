module Pretty



open Log
open Lang
open PPrint
open Parser
open Extensions



module Op =
  let pretty =
    function
    | Add          -> chr '+'
    | Sub          -> chr '-'
    | Mul          -> chr '*'
    | Div          -> chr '/'
    | Eq           -> txt "="
    | Ne           -> txt "<>"
    | Lt           -> chr '<'
    | Gt           -> chr '>'
    | Le           -> txt "<="
    | Ge           -> txt ">="
    | Or           -> txt "||"
    | And          -> txt "&&"
    | RefAsn       -> txt ":="
    | ListCons     -> txt "::"
    | ListConcat   -> chr '@'
    | StringConcat -> txt "++"



module Type =
  let rec pretty =
    function
    | TUnknown -> empty
    | TUser s  -> txt s
    | TVar  s  -> txt s
    | TUnit    -> txt "()"
    | TInt     -> txt "Int"
    | TBool    -> txt "Bool"
    | TString  -> txt "String"

    | TADT    (s, _) -> txt s
    | TRecord (s, _) -> txt s

    | TRef (TFun _ as t) -> cat [chr '&'; pretty t |> parens]
    | TRef t             -> cat [chr '&'; pretty t]

    | TArrow _ as t -> pretty (Type.arrowsToFuns t)

    | TFun ts ->
        let f =
          function
          | TFun(_) as t -> parens (pretty t)
          | t            -> pretty t

        Array.map f ts
        |> Array.intersperse (txt "->")
        |> sep


    | TTuple ts ->
        Array.map pretty ts
        |> Array.intersperse (txt ", ")
        |> cat
        |> parens

    | TList t   ->
        cat [ chr '['
            ; pretty t
            ; chr ']'
            ]

    | t -> failwithf "Error @ Type.pretty: %A" t



  let prettyString =
    pretty
    >> render



  let prettyPrint =
    prettyString
    >> printfn "%s"



module Param =
  let pretty =
    function
    | Untyped s -> txt s
    | Typed (s, t) ->
        match Type.flattenUnknowns t with
        | TUnknown -> txt s
        | t        ->
            sep [txt s
                ; chr ':'
                ; Type.pretty t
                ]
            |> parens



let prettyLetSig d s ps t =
  let retTy =
    match Type.flattenUnknowns t with
    | TUnknown -> empty
    | t        ->
        sep [ chr ':'
            ; Type.pretty t
            ]

  sep [ d
      ; txt s
      ; sep (Array.map Param.pretty ps)
      ; retTy
      ; chr '='
      ]



let prettyLetHead d1 s ps t d2 =
  sep [prettyLetSig d1 s ps t; d2]



module Expr =
  let rec pretty (p1 : int) (e : Expr) : Doc =
    let p2 = Expr.precedence e

    parensIf (p2 < p1) <|
    match e with
    | EVar s      -> txt s
    | EUnit       -> txt "()"
    | EBool true  -> txt "True"
    | EBool false -> txt "False"
    | EString s   -> dquotes (txt s)
    | EInt x      -> txt (sprintf "%d" x)

    | EFix e ->
        sep [ txt "fix"
            ; pretty 0 e |> parens
            ]

    | EBop (x, op, y) ->
        sep [ pretty p2 x
            ; Op.pretty op
            ; pretty p2 y
            ]

    | EApp (e1, e2) ->
        match e2 with
        | EApp _ -> sep [pretty p2 e1; pretty p2 e2 |> parens]
        |      _ -> sep [pretty p2 e1; pretty p2 e2]

    | ESeq es ->
        Array.map (pretty p2) es
        |> Array.intersperse (chr ';')
        |> Array.chunkBySize 2
        |> Array.map cat
        |> lines

    | EIf (e1, e2, e3) ->
        lines [ sep [txt "if"  ; pretty p2 e1]
              ; sep [txt "then"; pretty p2 e2] |> nest 2
              ; sep [txt "else"; pretty p2 e3] |> nest 2
              ]

    | ELambda (ps, e) ->
        lines [ sep [ txt "fun"
                    ; Array.map Param.pretty ps |> sep
                    ; txt "->"
                    ]
              ; pretty p2 e |> nest 2
              ]

    | ERef    i -> txt (sprintf "<loc: %i>" i)
    | EDeRef  e -> cat [chr '!'; pretty p2 e]
    | ERefLit e -> cat [chr '&'; pretty p2 e]

    | EProjAgg (e1, e2) ->
        cat [ pretty p2 e1
            ; txt ".["
            ; pretty 0  e2
            ; chr ']'
            ]

    | EProjRec (e, s) ->
        cat [ pretty p2 e
            ; chr '.'
            ; txt s
            ]

    | ETuple es ->
        Array.map (pretty 0) es
        |> sepList (chr ',')
        |> parens

    | EList es ->
        Array.map (pretty 0) es
        |> sepList (chr ',')
        |> brackets

    | ETopLet (s, ps, t, e) ->
        lines [ prettyLetSig (txt "let") s ps t
              ; pretty p2 e |> nest 2
              ]

    | ETopLetRec (s, ps, t, e) ->
        lines [ prettyLetSig (txt "let rec") s ps t
              ; pretty p2 e |> nest 2
              ]

    | ELet (s, ps, t, e1, e2) ->
        lines [ pretty p2 e1
                |> prettyLetHead (txt "let") s ps t

              ; sep [txt "in"; pretty p2 e2]
              ]

    | ELetRec (s, ps, t, e1, e2) ->
        lines [ pretty p2 e1
                |> prettyLetHead (txt "let rec") s ps t

              ; sep [txt "in"; pretty p2 e2]
              ]

    | EConstructor s -> txt s

    | EDefRecord (s, xs) ->
        let head =
          sep [txt "type"
              ; txt s
              ; chr '='
              ]

        let f (s2, t) =
          sep [ txt s2
              ; chr ':'
              ; Type.pretty t
              ]

        match xs with
        | [| |] -> failwith "Error @ Expr.pretty: []"
        | [|x|] -> sep [head; f x |> braces]
        | xs    ->
            let y  = sep [chr '{'; f xs.[0]]
            let ys = Array.map (fun x -> sep [chr ','; f x]) xs.[1 ..]
            let z  = chr '}'

            Array.concat [[|y|]; ys; [|z|]]
            |> Array.map (nest 2)
            |> Array.append [|head|]
            |> lines

    | EDefADT (s, xs) ->
        let head =
          sep [ txt "type"
              ; txt s
              ; chr '='
              ]

        let f (s2, ts) =
          match ts with
          | [| |] -> txt s2
          | [|t|] -> sep [|txt s2; chr ':'; Type.pretty t|]
          | _     ->
            Type.pretty (TTuple ts)
            |> Array.snoc [|txt s2; chr ':'|]
            |> sep

        match xs with
        | [|x|] -> sep [head; f x]
        | xs    ->
           let g x =
             sep [chr '|'; f x]
             |> nest 2

           Array.map g xs
           |> Array.append [|head|]
           |> lines

    | ERecordLit xs  ->
        let f (s2, e) =
          sep [ txt s2
              ; chr '='
              ; pretty 0 e
              ]

        match xs with
        | [| |] -> failwith "Error2 @ Expr.pretty: []"
        | [|x|] -> braces (f x)
        | xs    ->
            Array.map f xs
            |> sepList (chr ',')
            |> braces

    | EMatch (e1, xs) ->
        let head =
          sep [ txt "match"
              ; pretty 0 e1 |> parens
              ; chr '{'
              ]

        let f (p, e2) =
          sep [ chr '|'
              ; pretty p2 (Expr.ofPattern p)
              ; txt "->"
              ; pretty p2 e2
              ]

        [[|head|]; Array.map f xs; [|chr '}'|]]
        |> Array.concat
        |> lines



  let prettyString =
    pretty 0
    >> render



  let prettyPrint =
    prettyString
    >> printfn "%s"



module Core =
  let prettyString =
    Expr.ofCore
    >> Expr.prettyString



  let prettyPrint =
    prettyString
    >> printfn "%s"



module Pattern =
  let prettyStringPattern =
    Expr.ofPattern
    >> Expr.prettyString



module AST =
  let prettyPrint =
    function
    | Prgm es -> Array.iter (Expr.prettyString >> printfn "%s\n") es
    | Expr e  -> Expr.prettyString e |> printfn "%s\n"
    | Empty   -> printfn "{}"



let ppr s =
  match parse s with
  | AST (Prgm es) ->
      let f =
        Expr.prettyString
        >> printfn "%s"

      Array.iter f es

  | AST (Expr e1) ->
      Expr.prettyString e1
      |> printfn "%s"

  | AST Empty -> printfn "{}"
  | Error s   -> printfn "%s" s



let test1 _ = ppr "let f (x : Int) : Int = \
                     let y = x \
                     in if false \
                          then y \
                          else match (x) {
                               | 0 -> x \
                               | _ ->  1337 \
                               }"
