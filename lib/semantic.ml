open Ast

module StringMap = Map.Make(String)

type sym_info = {
  sym_type: typ;
  is_const: bool;
  is_global: bool;
  const_value: int option;
}

type func_info = {
  func_ret_type: typ;
  func_params: typ list;
}

type env = {
  scopes: sym_info StringMap.t list;
  functions: func_info StringMap.t;
  current_func: typ option;
  in_loop: bool;
}

let empty_env = {
  scopes = [StringMap.empty];
  functions = StringMap.empty;
  current_func = None;
  in_loop = false;
}

let push_scope env =
  { env with scopes = StringMap.empty :: env.scopes }

let pop_scope env =
  match env.scopes with
  | _ :: rest -> { env with scopes = rest }
  | [] -> failwith "Cannot pop global scope"

let add_symbol name info env =
  match env.scopes with
  | current :: rest ->
    { env with scopes = StringMap.add name info current :: rest }
  | [] -> failwith "No scope"

let lookup name env =
  let rec find = function
    | [] -> None
    | scope :: rest ->
      match StringMap.find_opt name scope with
      | Some _ as r -> r
      | None -> find rest
  in
  find env.scopes

let add_function name info env =
  { env with functions = StringMap.add name info env.functions }

let lookup_function name env =
  StringMap.find_opt name env.functions

let rec eval_const_expr env = function
  | IntLit n -> Some n
  | Id name ->
    (match lookup name env with
     | Some { is_const = true; const_value = Some v; _ } -> Some v
     | _ -> None)
  | BinOp (op, l, r) ->
    (match eval_const_expr env l, eval_const_expr env r with
     | Some lv, Some rv ->
       (match op with
        | Add -> Some (lv + rv)
        | Sub -> Some (lv - rv)
        | Mul -> Some (lv * rv)
        | Div -> if rv <> 0 then Some (lv / rv) else None
        | Mod -> if rv <> 0 then Some (lv mod rv) else None
        | _ -> None)
     | _ -> None)
  | UnaryOp (Neg, e) ->
    (match eval_const_expr env e with
     | Some n -> Some (-n)
     | None -> None)
  | _ -> None

let rec check_expr env = function
  | IntLit _ -> Int
  | Id name ->
    (match lookup name env with
     | Some info -> info.sym_type
     | None -> failwith ("Undeclared variable: " ^ name))
  | BinOp (_, l, r) ->
    ignore (check_expr env l);
    ignore (check_expr env r);
    Int
  | UnaryOp (_, e) ->
    ignore (check_expr env e);
    Int
  | Call (name, args) ->
    (match lookup_function name env with
     | Some fi ->
       if List.length fi.func_params <> List.length args then
         failwith ("Argument count mismatch for function: " ^ name);
       List.iter (fun e -> ignore (check_expr env e)) args;
       fi.func_ret_type
     | None -> failwith ("Undeclared function: " ^ name))

let rec check_stmt env = function
  | Block stmts ->
    let inner = push_scope env in
    List.fold_left check_stmt inner stmts |> ignore;
    env
  | Empty -> env
  | ExprStmt e ->
    ignore (check_expr env e);
    env
  | Assign (name, e) ->
    (match lookup name env with
     | Some { is_const = true; _ } ->
       failwith ("Cannot assign to constant: " ^ name)
     | Some _ ->
       ignore (check_expr env e);
       env
     | None -> failwith ("Undeclared variable: " ^ name))
  | DeclStmt (ConstDecl (name, e)) ->
    ignore (check_expr env e);
    add_symbol name { sym_type = Int; is_const = true; is_global = false; const_value = None } env
  | DeclStmt (VarDecl (name, e)) ->
    ignore (check_expr env e);
    add_symbol name { sym_type = Int; is_const = false; is_global = false; const_value = None } env
  | If (cond, s1, s2) ->
    ignore (check_expr env cond);
    ignore (check_stmt env s1);
    (match s2 with
     | Some s -> ignore (check_stmt env s)
     | None -> ());
    env
  | While (cond, body) ->
    ignore (check_expr env cond);
    let loop_env = { env with in_loop = true } in
    ignore (check_stmt loop_env body);
    env
  | Break ->
    if not env.in_loop then failwith "break outside loop";
    env
  | Continue ->
    if not env.in_loop then failwith "continue outside loop";
    env
  | Return e_opt ->
    (match env.current_func, e_opt with
     | Some Void, Some _ -> failwith "void function returns a value"
     | Some Int, None -> failwith "int function must return a value"
     | Some _, Some e -> ignore (check_expr env e)
     | Some Void, None -> ()
     | None, _ -> failwith "return outside function");
    env

let check_func_def env fd =
  let params_types = List.map (fun _ -> Int) fd.params in
  let fi = { func_ret_type = fd.ret_type; func_params = params_types } in
  let env' = add_function fd.name fi env in
  let func_env = { env' with current_func = Some fd.ret_type } in
  let func_env = List.fold_left
    (fun e p -> add_symbol p { sym_type = Int; is_const = false; is_global = false; const_value = None } e)
    func_env fd.params
  in
  let _ = List.fold_left check_stmt func_env fd.body in
  env'

let check_program prog =
  let env = empty_env in
  (* First pass: register all functions *)
  let env = List.fold_left (fun e item ->
    match item with
    | FuncDef fd ->
      let params_types = List.map (fun _ -> Int) fd.params in
      let fi = { func_ret_type = fd.ret_type; func_params = params_types } in
      add_function fd.name fi e
    | FuncDecl fd ->
      let params_types = List.map (fun _ -> Int) fd.params in
      let fi = { func_ret_type = fd.ret_type; func_params = params_types } in
      add_function fd.name fi e
    | GlobalDecl _ -> e
  ) env prog in
  (* Second pass: check everything *)
  let env = List.fold_left (fun e item ->
    match item with
    | GlobalDecl (ConstDecl (name, init)) ->
      ignore (check_expr e init);
      let const_val = eval_const_expr e init in
      add_symbol name { sym_type = Int; is_const = true; is_global = true; const_value = const_val } e
    | GlobalDecl (VarDecl (name, init)) ->
      ignore (check_expr e init);
      let const_val = eval_const_expr e init in
      add_symbol name { sym_type = Int; is_const = false; is_global = true; const_value = const_val } e
    | FuncDef fd -> check_func_def e fd
    | FuncDecl _ -> e
  ) env prog in
  (* Check main function exists *)
  match lookup_function "main" env with
  | Some { func_ret_type = Int; func_params = []; _ } -> ()
  | Some _ -> failwith "main must be: int main()"
  | None -> failwith "No main function"
