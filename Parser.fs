module Parser

open Microsoft.FSharp.Text.Lexing
open ParserImpl
open LexerImpl
open Lang



type ParserResult
  = AST of AST
  | Error of string



let parse (s: string) =
  let lexbuf = LexBuffer<char>.FromString s

  try
    AST (ParserImpl.start LexerImpl.tokenize lexbuf)
  with
    | LexException s -> Error s
    | _ ->
      let s   = LexBuffer<char>.LexemeString lexbuf
      let ln  = lexbuf.StartPos.Line + 1
      let col = lexbuf.StartPos.Column
      sprintf "Syntax error: unexpected '%s' @ ln %d, col %d" s ln col
      |> Error
