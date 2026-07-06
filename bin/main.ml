let () =
  let lexbuf = Lexing.from_channel stdin in
  try
    let prog = Parser.program Lexer.token lexbuf in
    Semantic.check_program prog;
    let asm = Codegen.gen_program prog in
    print_string asm
  with
  | Failure msg ->
    Printf.eprintf "Error: %s\n" msg;
    exit 1
  | Parsing.Parse_error ->
    let pos = lexbuf.lex_curr_p in
    Printf.eprintf "Syntax error at line %d, column %d\n"
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
    exit 1
