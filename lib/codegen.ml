open Ast

module StringMap = Map.Make(String)

type ctx = {
  buf: Buffer.t;
  mutable label_count: int;
  mutable var_offsets: int StringMap.t list;
  mutable frame_offset: int;
  mutable break_label: string option;
  mutable continue_label: string option;
  mutable func_ret_label: string option;
}

let new_label ctx prefix =
  ctx.label_count <- ctx.label_count + 1;
  Printf.sprintf "%s_%d" prefix ctx.label_count

let emit ctx fmt =
  Printf.bprintf ctx.buf (fmt ^^ "\n")

let rec eval_const_expr globals = function
  | IntLit n -> Some n
  | Id name ->
    (match StringMap.find_opt name globals with
     | Some v -> Some v
     | None -> None)
  | BinOp (op, l, r) ->
    (match eval_const_expr globals l, eval_const_expr globals r with
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
    (match eval_const_expr globals e with
     | Some n -> Some (-n)
     | None -> None)
  | _ -> None

let push_scope ctx =
  ctx.var_offsets <- StringMap.empty :: ctx.var_offsets

let pop_scope ctx =
  match ctx.var_offsets with
  | _ :: rest -> ctx.var_offsets <- rest
  | [] -> failwith "Cannot pop global scope"

let add_var ctx name =
  ctx.frame_offset <- ctx.frame_offset - 4;
  let off = ctx.frame_offset in
  emit ctx "  addi sp, sp, -4";
  match ctx.var_offsets with
  | current :: rest ->
    ctx.var_offsets <- StringMap.add name off current :: rest
  | [] -> failwith "No scope"

let lookup_var ctx name =
  let rec find = function
    | [] -> None
    | scope :: rest ->
      match StringMap.find_opt name scope with
      | Some _ as r -> r
      | None -> find rest
  in
  find ctx.var_offsets

let rec gen_expr ctx = function
  | IntLit n ->
    emit ctx "  li a0, %d" n
  | Id name ->
    (match lookup_var ctx name with
     | Some off ->
       emit ctx "  lw a0, %d(fp)" off
     | None ->
       (* Try to access as global variable *)
       emit ctx "  la t0, %s" name;
       emit ctx "  lw a0, 0(t0)")
   | BinOp (And, l, r) ->
     (* Short-circuit AND: evaluate left first, skip right if false *)
     let lend = new_label ctx "and_end" in
     gen_expr ctx l;
     emit ctx "  beqz a0, %s" lend;
     gen_expr ctx r;
     emit ctx "%s:" lend
   | BinOp (Or, l, r) ->
     (* Short-circuit OR: evaluate left first, skip right if true *)
     let lend = new_label ctx "or_end" in
     gen_expr ctx l;
     emit ctx "  bnez a0, %s" lend;
     gen_expr ctx r;
     emit ctx "%s:" lend
   | BinOp (op, l, r) ->
     (* Try constant folding *)
     let lv = eval_const_expr StringMap.empty l in
     let rv = eval_const_expr StringMap.empty r in
     (match lv, rv, op with
      | Some lv, Some rv, Add -> emit ctx "  li a0, %d" (lv + rv)
      | Some lv, Some rv, Sub -> emit ctx "  li a0, %d" (lv - rv)
      | Some lv, Some rv, Mul -> emit ctx "  li a0, %d" (lv * rv)
      | Some lv, Some rv, Div when rv <> 0 -> emit ctx "  li a0, %d" (lv / rv)
      | Some lv, Some rv, Mod when rv <> 0 -> emit ctx "  li a0, %d" (lv mod rv)
      | Some lv, Some rv, Lt -> emit ctx "  li a0, %d" (if lv < rv then 1 else 0)
      | Some lv, Some rv, Gt -> emit ctx "  li a0, %d" (if lv > rv then 1 else 0)
      | Some lv, Some rv, Le -> emit ctx "  li a0, %d" (if lv <= rv then 1 else 0)
      | Some lv, Some rv, Ge -> emit ctx "  li a0, %d" (if lv >= rv then 1 else 0)
      | Some lv, Some rv, Eq -> emit ctx "  li a0, %d" (if lv = rv then 1 else 0)
      | Some lv, Some rv, Neq -> emit ctx "  li a0, %d" (if lv <> rv then 1 else 0)
      | _, Some 0, Add -> gen_expr ctx l
      | Some 0, _, Add -> gen_expr ctx r
      | _, Some 0, Sub -> gen_expr ctx l
      | Some 0, _, Mul -> emit ctx "  li a0, 0"
      | _, Some 0, Mul -> emit ctx "  li a0, 0"
      | Some 1, _, Mul -> gen_expr ctx r
      | _, Some 1, Mul -> gen_expr ctx l
      | _, Some 1, Div -> gen_expr ctx l
      | _, Some 1, Mod -> emit ctx "  li a0, 0"
      | _, Some n, Mul when n > 0 && (n land (n-1)) = 0 ->
        gen_expr ctx l;
        let rec pow2 k acc = if acc = n then k else pow2 (k+1) (acc*2) in
        emit ctx "  slli a0, a0, %d" (pow2 0 1)
      | _, Some n, Add when n >= -2048 && n <= 2047 ->
        gen_expr ctx l;
        emit ctx "  addi a0, a0, %d" n
      | Some n, _, Add when n >= -2048 && n <= 2047 ->
        gen_expr ctx r;
        emit ctx "  addi a0, a0, %d" n
      | _, Some n, Sub when n >= -2048 && n <= 2047 ->
        gen_expr ctx l;
        emit ctx "  addi a0, a0, %d" (-n)
      | _ ->
        gen_expr ctx r;
        emit ctx "  addi sp, sp, -4";
        emit ctx "  sw a0, 0(sp)";
        gen_expr ctx l;
        emit ctx "  lw t1, 0(sp)";
        emit ctx "  addi sp, sp, 4";
        (match op with
         | Add -> emit ctx "  add a0, a0, t1"
         | Sub -> emit ctx "  sub a0, a0, t1"
         | Mul -> emit ctx "  mul a0, a0, t1"
         | Div -> emit ctx "  div a0, a0, t1"
         | Mod -> emit ctx "  rem a0, a0, t1"
         | Lt -> emit ctx "  slt a0, a0, t1"
         | Gt -> emit ctx "  slt a0, t1, a0"
         | Le -> emit ctx "  slt a0, t1, a0"; emit ctx "  xori a0, a0, 1"
         | Ge -> emit ctx "  slt a0, a0, t1"; emit ctx "  xori a0, a0, 1"
         | Eq -> emit ctx "  sub a0, a0, t1"; emit ctx "  seqz a0, a0"
         | Neq -> emit ctx "  sub a0, a0, t1"; emit ctx "  snez a0, a0"
         | And | Or -> failwith "unreachable"))
  | UnaryOp (op, e) ->
    gen_expr ctx e;
    (match op with
     | Neg -> emit ctx "  neg a0, a0"
     | Not -> emit ctx "  seqz a0, a0")
   | Call (name, args) ->
     let nargs = List.length args in
     (* Allocate space for all arguments + ra *)
     let save_size = (nargs + 1) * 4 in
     emit ctx "  addi sp, sp, -%d" save_size;
     emit ctx "  sw ra, %d(sp)" (save_size - 4);
     (* Evaluate all arguments and store on stack *)
     List.iteri (fun i arg ->
       gen_expr ctx arg;
       emit ctx "  sw a0, %d(sp)" (i * 4)
     ) args;
     (* Load first 8 arguments into registers *)
     for i = 0 to min 7 (nargs - 1) do
       emit ctx "  lw a%d, %d(sp)" i (i * 4)
     done;
     emit ctx "  call %s" name;
     emit ctx "  lw ra, %d(sp)" (save_size - 4);
     emit ctx "  addi sp, sp, %d" save_size

let rec gen_stmt ctx = function
  | Block stmts ->
    push_scope ctx;
    let saved_offset = ctx.frame_offset in
    List.iter (gen_stmt ctx) stmts;
    let allocated = saved_offset - ctx.frame_offset in
    if allocated > 0 then
      emit ctx "  addi sp, sp, %d" allocated;
    ctx.frame_offset <- saved_offset;
    pop_scope ctx
  | Empty -> ()
  | ExprStmt e -> gen_expr ctx e
  | Assign (name, e) ->
    gen_expr ctx e;
    (match lookup_var ctx name with
     | Some off -> emit ctx "  sw a0, %d(fp)" off
     | None ->
       (* Try to assign to global variable *)
       emit ctx "  la t0, %s" name;
       emit ctx "  sw a0, 0(t0)")
  | DeclStmt (ConstDecl (name, e)) ->
    gen_expr ctx e;
    add_var ctx name;
    (match lookup_var ctx name with
     | Some off -> emit ctx "  sw a0, %d(fp)" off
     | None -> ())
  | DeclStmt (VarDecl (name, e)) ->
    gen_expr ctx e;
    add_var ctx name;
    (match lookup_var ctx name with
     | Some off -> emit ctx "  sw a0, %d(fp)" off
     | None -> ())
  | If (cond, s1, s2) ->
    (match s2 with
     | Some s2 ->
       let lfalse = new_label ctx "if_false" in
       let lend = new_label ctx "if_end" in
       gen_expr ctx cond;
       emit ctx "  beqz a0, %s" lfalse;
       gen_stmt ctx s1;
       emit ctx "  j %s" lend;
       emit ctx "%s:" lfalse;
       gen_stmt ctx s2;
       emit ctx "%s:" lend
     | None ->
       let lend = new_label ctx "if_end" in
       gen_expr ctx cond;
       emit ctx "  beqz a0, %s" lend;
       gen_stmt ctx s1;
       emit ctx "%s:" lend)
  | While (cond, body) ->
    let lstart = new_label ctx "while_start" in
    let lend = new_label ctx "while_end" in
    let prev_break = ctx.break_label in
    let prev_continue = ctx.continue_label in
    ctx.break_label <- Some lend;
    ctx.continue_label <- Some lstart;
    emit ctx "%s:" lstart;
    gen_expr ctx cond;
    emit ctx "  beqz a0, %s" lend;
    gen_stmt ctx body;
    emit ctx "  j %s" lstart;
    emit ctx "%s:" lend;
    ctx.break_label <- prev_break;
    ctx.continue_label <- prev_continue
  | Break ->
    (match ctx.break_label with
     | Some l -> emit ctx "  j %s" l
     | None -> failwith "break outside loop")
  | Continue ->
    (match ctx.continue_label with
     | Some l -> emit ctx "  j %s" l
     | None -> failwith "continue outside loop")
  | Return e_opt ->
    (match e_opt with
     | Some e -> gen_expr ctx e
     | None -> emit ctx "  li a0, 0");
    (match ctx.func_ret_label with
     | Some l -> emit ctx "  j %s" l
     | None -> failwith "return outside function")

let gen_func_def ctx fd =
  let ret_label = new_label ctx "ret" in
  let old_ret = ctx.func_ret_label in
  ctx.func_ret_label <- Some ret_label;
  let old_offset = ctx.frame_offset in
  ctx.frame_offset <- 0;
  push_scope ctx;
  emit ctx "";
  emit ctx ".globl %s" fd.name;
  emit ctx "%s:" fd.name;
  (* Prologue: save ra and fp *)
  emit ctx "  addi sp, sp, -8";
  emit ctx "  sw ra, 4(sp)";
  emit ctx "  sw fp, 0(sp)";
  emit ctx "  mv fp, sp";
  (* Store register parameters to stack *)
  let params = Array.of_list fd.params in
  let nparams = Array.length params in
  let reg_params = min nparams 8 in
  (* Allocate space for parameters *)
  let param_space = reg_params * 4 in
  if param_space > 0 then
    emit ctx "  addi sp, sp, -%d" param_space;
  (* Store parameters at sp-relative offsets, but record fp-relative offsets *)
  for i = 0 to reg_params - 1 do
    let sp_off = i * 4 in
    let fp_off = sp_off - param_space in
    emit ctx "  sw a%d, %d(sp)" i sp_off;
    match ctx.var_offsets with
    | current :: rest ->
      ctx.var_offsets <- StringMap.add params.(i) fp_off current :: rest
    | [] -> failwith "No scope"
  done;
  (* Local variables start below parameters *)
  ctx.frame_offset <- -param_space;
  (* Stack parameters are at fp+40, fp+44, etc. (8 for ra/fp + 32 for register params) *)
  for i = 8 to nparams - 1 do
    let off = 40 + (i - 8) * 4 in
    match ctx.var_offsets with
    | current :: rest ->
      ctx.var_offsets <- StringMap.add params.(i) off current :: rest
    | [] -> failwith "No scope"
  done;
  List.iter (gen_stmt ctx) fd.body;
  emit ctx "%s:" ret_label;
  emit ctx "  mv sp, fp";
  emit ctx "  lw fp, 0(sp)";
  emit ctx "  lw ra, 4(sp)";
  emit ctx "  addi sp, sp, 8";
  emit ctx "  ret";
  pop_scope ctx;
  ctx.frame_offset <- old_offset;
  ctx.func_ret_label <- old_ret

let gen_program prog =
  let ctx = {
    buf = Buffer.create 4096;
    label_count = 0;
    var_offsets = [StringMap.empty];
    frame_offset = 0;
    break_label = None;
    continue_label = None;
    func_ret_label = None;
  } in
  (* First pass: collect global constant values *)
  let globals = List.fold_left (fun acc item ->
    match item with
    | GlobalDecl (ConstDecl (name, init)) ->
      (match eval_const_expr acc init with
       | Some v -> StringMap.add name v acc
       | None -> acc)
    | GlobalDecl (VarDecl (name, init)) ->
      (match eval_const_expr acc init with
       | Some v -> StringMap.add name v acc
       | None -> acc)
    | _ -> acc
  ) StringMap.empty prog in
  (* Generate data section for global variables *)
  let global_defs = List.filter_map (fun item ->
    match item with
    | GlobalDecl (VarDecl (name, init)) ->
      (match eval_const_expr globals init with
       | Some n -> Some (name, n)
       | None -> None)
    | GlobalDecl (ConstDecl (name, init)) ->
      (match eval_const_expr globals init with
       | Some n -> Some (name, n)
       | None -> None)
    | _ -> None
  ) prog in
  if global_defs <> [] then begin
    emit ctx ".data";
    List.iter (fun (name, n) ->
      emit ctx ".globl %s" name;
      emit ctx "%s:" name;
      emit ctx "  .word %d" n
    ) global_defs
  end;
  emit ctx ".text";
  List.iter (fun item ->
    match item with
    | FuncDef fd -> gen_func_def ctx fd
    | GlobalDecl _ -> ()
    | FuncDecl _ -> ()
  ) prog;
  Buffer.contents ctx.buf
