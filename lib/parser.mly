%{
open Ast
%}

%token <int> NUMBER
%token <string> ID
%token CONST INT VOID IF ELSE WHILE BREAK CONTINUE RETURN
%token LPAREN RPAREN LBRACE RBRACE COMMA SEMICOLON ASSIGN
%token PLUS MINUS STAR SLASH PERCENT
%token LT GT LE GE EQ NEQ
%token AND OR NOT
%token EOF

%left OR
%left AND
%nonassoc LT GT LE GE EQ NEQ
%left PLUS MINUS
%left STAR SLASH PERCENT
%right UMINUS UNOT

%start <Ast.program> program

%%

program:
  | cs = comp_unit_items EOF { cs }

comp_unit_items:
  | c = comp_unit_item { [c] }
  | cs = comp_unit_items c = comp_unit_item { cs @ [c] }

comp_unit_item:
  | d = global_decl { GlobalDecl d }
  | f = func_def { FuncDef f }

global_decl:
  | CONST INT name = ID ASSIGN init = expr SEMICOLON { ConstDecl (name, init) }
  | INT name = ID ASSIGN init = expr SEMICOLON { VarDecl (name, init) }

func_def:
  | INT name = ID LPAREN params = separated_list(COMMA, param) RPAREN body = block
    { { ret_type = Int; name; params; body } }
  | VOID name = ID LPAREN params = separated_list(COMMA, param) RPAREN body = block
    { { ret_type = Void; name; params; body } }

param:
  | INT name = ID { name }

block:
  | LBRACE ss = stmt* RBRACE { ss }

stmt:
  | b = block { Block b }
  | SEMICOLON { Empty }
  | e = expr SEMICOLON { ExprStmt e }
  | name = ID ASSIGN e = expr SEMICOLON { Assign (name, e) }
  | d = local_decl { DeclStmt d }
  | IF LPAREN cond = expr RPAREN s = stmt { If (cond, s, None) }
  | IF LPAREN cond = expr RPAREN s1 = stmt ELSE s2 = stmt { If (cond, s1, Some s2) }
  | WHILE LPAREN cond = expr RPAREN s = stmt { While (cond, s) }
  | BREAK SEMICOLON { Break }
  | CONTINUE SEMICOLON { Continue }
  | RETURN SEMICOLON { Return None }
  | RETURN e = expr SEMICOLON { Return (Some e) }

local_decl:
  | CONST INT name = ID ASSIGN init = expr SEMICOLON { ConstDecl (name, init) }
  | INT name = ID ASSIGN init = expr SEMICOLON { VarDecl (name, init) }

expr:
  | e = lor_expr { e }

lor_expr:
  | e = land_expr { e }
  | l = lor_expr OR r = land_expr { BinOp (Or, l, r) }

land_expr:
  | e = rel_expr { e }
  | l = land_expr AND r = rel_expr { BinOp (And, l, r) }

rel_expr:
  | e = add_expr { e }
  | l = rel_expr LT r = add_expr { BinOp (Lt, l, r) }
  | l = rel_expr GT r = add_expr { BinOp (Gt, l, r) }
  | l = rel_expr LE r = add_expr { BinOp (Le, l, r) }
  | l = rel_expr GE r = add_expr { BinOp (Ge, l, r) }
  | l = rel_expr EQ r = add_expr { BinOp (Eq, l, r) }
  | l = rel_expr NEQ r = add_expr { BinOp (Neq, l, r) }

add_expr:
  | e = mul_expr { e }
  | l = add_expr PLUS r = mul_expr { BinOp (Add, l, r) }
  | l = add_expr MINUS r = mul_expr { BinOp (Sub, l, r) }

mul_expr:
  | e = unary_expr { e }
  | l = mul_expr STAR r = unary_expr { BinOp (Mul, l, r) }
  | l = mul_expr SLASH r = unary_expr { BinOp (Div, l, r) }
  | l = mul_expr PERCENT r = unary_expr { BinOp (Mod, l, r) }

unary_expr:
  | e = primary_expr { e }
  | MINUS e = unary_expr %prec UMINUS { UnaryOp (Neg, e) }
  | NOT e = unary_expr %prec UNOT { UnaryOp (Not, e) }

primary_expr:
  | n = NUMBER { IntLit n }
  | name = ID { Id name }
  | LPAREN e = expr RPAREN { e }
  | name = ID LPAREN args = separated_list(COMMA, expr) RPAREN { Call (name, args) }
