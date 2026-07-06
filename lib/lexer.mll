{
open Parser
open Lexing

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with
    pos_lnum = pos.pos_lnum + 1;
    pos_bol = pos.pos_cnum;
  }
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z' '_']
let id = alpha (alpha | digit)*
let num = digit+

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n'             { next_line lexbuf; token lexbuf }
  | "//"             { single_line_comment lexbuf }
  | "/*"             { multi_line_comment lexbuf }
  | num as n         { NUMBER (int_of_string n) }
  | "const"          { CONST }
  | "int"            { INT }
  | "void"           { VOID }
  | "if"             { IF }
  | "else"           { ELSE }
  | "while"          { WHILE }
  | "break"          { BREAK }
  | "continue"       { CONTINUE }
  | "return"         { RETURN }
  | id as s          { ID s }
  | "("              { LPAREN }
  | ")"              { RPAREN }
  | "{"              { LBRACE }
  | "}"              { RBRACE }
  | ","              { COMMA }
  | ";"              { SEMICOLON }
  | "="              { ASSIGN }
  | "+"              { PLUS }
  | "-"              { MINUS }
  | "*"              { STAR }
  | "/"              { SLASH }
  | "%"              { PERCENT }
  | "<"              { LT }
  | ">"              { GT }
  | "<="             { LE }
  | ">="             { GE }
  | "=="             { EQ }
  | "!="             { NEQ }
  | "&&"             { AND }
  | "||"             { OR }
  | "!"              { NOT }
  | eof              { EOF }
  | _                { failwith ("Unexpected char: " ^ Lexing.lexeme lexbuf) }

and single_line_comment = parse
  | '\n' { next_line lexbuf; token lexbuf }
  | eof  { EOF }
  | _    { single_line_comment lexbuf }

and multi_line_comment = parse
  | "*/" { token lexbuf }
  | '\n' { next_line lexbuf; multi_line_comment lexbuf }
  | eof  { failwith "Unterminated comment" }
  | _    { multi_line_comment lexbuf }
