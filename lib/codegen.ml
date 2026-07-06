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
  | BinOp (op, l, r) ->
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
     | Le ->
       emit ctx "  slt a0, t1, a0";
       emit ctx "  xori a0, a0, 1"
     | Ge ->
       emit ctx "  slt a0, a0, t1";
       emit ctx "  xori a0, a0, 1"
     | Eq ->
       emit ctx "  sub a0, a0, t1";
       emit ctx "  seqz a0, a0"
     | Neq ->
       emit ctx "  sub a0, a0, t1";
       emit ctx "  snez a0, a0"
     | And ->
       let lend = new_label ctx "and_end" in
       emit ctx "  beqz a0, %s" lend;
       emit ctx "  mv a0, t1";
       emit ctx "%s:" lend
     | Or ->
       let lend = new_label ctx "or_end" in
       emit ctx "  bnez a0, %s" lend;
       emit ctx "  mv a0, t1";
       emit ctx "%s:" lend)
  | UnaryOp (op, e) ->
    gen_expr ctx e;
    (match op with
     | Neg -> emit ctx "  neg a0, a0"
     | Not -> emit ctx "  seqz a0, a0")
  | Call (name, args) ->
    let nargs = List.length args in
    let stack_args = max 0 (nargs - 8) in
    (* Allocate space for extra arguments + ra *)
    let save_size = (stack_args + 1) * 4 in
    emit ctx "  addi sp, sp, -%d" save_size;
    emit ctx "  sw ra, %d(sp)" (save_size - 4);
    (* Evaluate and store extra arguments (beyond 8) at sp+0, sp+4, etc. *)
    for i = 8 to nargs - 1 do
      let arg = List.nth args i in
      gen_expr ctx arg;
      emit ctx "  sw a0, %d(sp)" ((i - 8) * 4)
    done;
    (* Evaluate and load first 8 arguments into registers *)
    for i = min 7 (nargs - 1) downto 0 do
      let arg = List.nth args i in
      gen_expr ctx arg;
      emit ctx "  mv a%d, a0" i
    done;
    emit ctx "  call %s" name;
    emit ctx "  lw ra, %d(sp)" (save_size - 4);
    emit ctx "  addi sp, sp, %d" save_size

let rec gen_stmt ctx = function
  | Block stmts ->
    push_scope ctx;
    List.iter (gen_stmt ctx) stmts;
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
  (* Stack parameters are at fp+8, fp+12, etc. *)
  for i = 8 to nparams - 1 do
    let off = 8 + (i - 8) * 4 in
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
  (* Generate data section for global variables *)
  let globals = List.filter_map (fun item ->
    match item with
    | GlobalDecl (VarDecl (name, IntLit n)) -> Some (name, n)
    | GlobalDecl (ConstDecl (name, IntLit n)) -> Some (name, n)
    | _ -> None
  ) prog in
  if globals <> [] then begin
    emit ctx ".data";
    List.iter (fun (name, n) ->
      emit ctx ".globl %s" name;
      emit ctx "%s:" name;
      emit ctx "  .word %d" n
    ) globals
  end;
  emit ctx ".text";
  List.iter (fun item ->
    match item with
    | FuncDef fd -> gen_func_def ctx fd
    | GlobalDecl _ -> ()
  ) prog;
  Buffer.contents ctx.buf
