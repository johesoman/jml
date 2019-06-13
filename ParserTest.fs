module ParserTest



open Pretty
open Parser



let go s =
  match parse s with
  | AST x     -> AST.prettyPrint x
  | Error err -> printfn "%s" err
