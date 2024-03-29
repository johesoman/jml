// Signature file for parser generated by fsyacc
type token = 
  | DIVOP
  | MULOP
  | SUBOP
  | ADDOP
  | ANDOP
  | OROP
  | GEOP
  | LEOP
  | GTOP
  | LTOP
  | NEOP
  | EQOP
  | EQEQOP
  | RPAR
  | LPAR
  | DEREF
  | FATARROW
  | ARROW
  | FUN
  | ELSE
  | THEN
  | IF
  | IN
  | REC
  | LET
  | EOF
  | TRUE
  | FALSE
  | SEMI
  | COLON
  | REFASN
  | REF
  | AND
  | DOT
  | END
  | COMMA
  | RBRACE
  | LBRACE
  | RBRACK
  | LBRACK
  | COLONCOLON
  | BAR
  | TYPE
  | MATCH
  | ATSIGN
  | PLUSPLUS
  | INT of (int)
  | ID of (string)
  | NAME of (string)
  | STRING of (string)
type tokenId = 
    | TOKEN_DIVOP
    | TOKEN_MULOP
    | TOKEN_SUBOP
    | TOKEN_ADDOP
    | TOKEN_ANDOP
    | TOKEN_OROP
    | TOKEN_GEOP
    | TOKEN_LEOP
    | TOKEN_GTOP
    | TOKEN_LTOP
    | TOKEN_NEOP
    | TOKEN_EQOP
    | TOKEN_EQEQOP
    | TOKEN_RPAR
    | TOKEN_LPAR
    | TOKEN_DEREF
    | TOKEN_FATARROW
    | TOKEN_ARROW
    | TOKEN_FUN
    | TOKEN_ELSE
    | TOKEN_THEN
    | TOKEN_IF
    | TOKEN_IN
    | TOKEN_REC
    | TOKEN_LET
    | TOKEN_EOF
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_SEMI
    | TOKEN_COLON
    | TOKEN_REFASN
    | TOKEN_REF
    | TOKEN_AND
    | TOKEN_DOT
    | TOKEN_END
    | TOKEN_COMMA
    | TOKEN_RBRACE
    | TOKEN_LBRACE
    | TOKEN_RBRACK
    | TOKEN_LBRACK
    | TOKEN_COLONCOLON
    | TOKEN_BAR
    | TOKEN_TYPE
    | TOKEN_MATCH
    | TOKEN_ATSIGN
    | TOKEN_PLUSPLUS
    | TOKEN_INT
    | TOKEN_ID
    | TOKEN_NAME
    | TOKEN_STRING
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_prog
    | NONTERM_arrowSepType2
    | NONTERM_commaSepType1
    | NONTERM_type1
    | NONTERM_type2
    | NONTERM_type3
    | NONTERM_parameter
    | NONTERM_parameters
    | NONTERM_returnType
    | NONTERM_recDefRec
    | NONTERM_variantCase
    | NONTERM_variantRec
    | NONTERM_typeDef
    | NONTERM_tops
    | NONTERM_topLet
    | NONTERM_manyMatchCase
    | NONTERM_expr1
    | NONTERM_semiSepExpr3
    | NONTERM_expr2
    | NONTERM_expr3
    | NONTERM_expr4
    | NONTERM_expr5
    | NONTERM_expr6
    | NONTERM_expr7
    | NONTERM_expr8
    | NONTERM_expr9
    | NONTERM_expr10
    | NONTERM_expr11
    | NONTERM_expr12
    | NONTERM_commaSepExpr1
    | NONTERM_recordRow
    | NONTERM_commaSepRecordRow
    | NONTERM_expr13
    | NONTERM_pat1
    | NONTERM_pat2
    | NONTERM_commaSepPat1
    | NONTERM_pat3
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> (AST) 
