open Unix
open Bytes
open Int64
open Int32

module type Consumer = sig
  type t

  val begin_tp : t -> MFOTL.timestamp -> unit
  val tuple : t -> Table.schema -> string list -> unit
  val end_tp : t -> unit
  val command : t -> string -> Helper.commandParameter option -> unit
  val end_log : t -> unit
  val parse_error : t -> Lexing.position -> string -> unit
end

type server_state = {
  inp : in_channel;
  outp : out_channel;
  schema : Db.schema;
  mutable num_events : int;
}

(*
    ASSUMPTIONS: On this machine (in the C toolchain): int is 32 bits, double is IEEE 64 bits
    WARNING: If these assumptions are not met, the code below will horribly fail
*)

type cmd = NEW_EVENT | NEW_DATABASE | END_DATABASE | LATENCY_MARKER | EOF

let read_bytes st num =
  let buf = Bytes.create num in
  really_input !st.inp buf 0 num;
  buf

let write_bytes st num f =
  let buf = Bytes.create num in
  f buf;
  output_bytes !st.outp buf

let read_int st =
  let b = read_bytes st 4 in
  get_int32_ne b 0

let write_int st i = write_bytes st 4 (fun b -> Bytes.set_int32_ne b 0 i)
let write_int_64 st i = write_bytes st 8 (fun b -> Bytes.set_int64_ne b 0 i)

let write_cmd st = function
  | LATENCY_MARKER -> write_int st (Int32.of_int 4)
  | EOF -> write_int st (Int32.of_int 5)
  | _ -> failwith "only LATENCY_MARKER|EOF supported for writing"

let read_int64 st =
  let b = read_bytes st 8 in
  get_int64_ne b 0

let read_float st =
  let b = read_bytes st 8 in
  let asi = get_int64_ne b 0 in
  Int64.float_of_bits asi

let read_string st =
  let sz = Bytes.get_int32_ne (read_bytes st 4) 0 in
  Bytes.to_string (read_bytes st (Int32.to_int sz))

let read_elem_ty st =
  Predicate.(
    match Int32.to_int (read_int st) with
    | 1 -> TInt
    | 2 -> TFloat
    | 3 -> TStr
    | i -> failwith (Printf.sprintf "unknown tuple element type number %d" i))

let read_tuple_element st ty =
  let is_ty = read_elem_ty st in
  if ty = is_ty then
    Predicate.(
      match ty with
      | TInt -> Int64.to_string (read_int64 st)
      | TFloat -> Float.to_string (read_float st)
      | TStr -> read_string st
      | TRegexp -> failwith "regexp not supported")
  else failwith "types do not match"

let read_tuple st =
  let pred_name = read_string st in
  let arity = Int32.to_int (read_int st) in
  assert (arity > 0);
  match List.assoc_opt pred_name !st.schema with
  | Some tys ->
      assert (arity = List.length tys);
      !st.num_events <- !st.num_events + 1;
      let tup = List.map (fun (_, ty) -> read_tuple_element st ty) tys in
      (pred_name, tup)
  | None -> failwith (Printf.sprintf "unknown predicate %s" pred_name)

let read_cmd st =
  match Int32.to_int (read_int st) with
  | 1 -> NEW_EVENT
  | 2 -> NEW_DATABASE
  | 3 -> END_DATABASE
  | 4 -> LATENCY_MARKER
  | 5 -> EOF
  | i -> failwith (Printf.sprintf "unknown cmd number %d" i)

module Make (C : Consumer) = struct
  let send_back_lm st lm =
    write_cmd st LATENCY_MARKER;
    write_int_64 st lm;
    flush !st.outp

  let send_eof ctx st =
    write_cmd st EOF;
    flush !st.outp

  let rec read_tuple_list ctx st =
    match read_cmd st with
    | NEW_EVENT ->
        let pred_name, tuple = read_tuple st in
        let tsc = List.assoc pred_name !st.schema in
        C.tuple ctx (pred_name, tsc) tuple;
        read_tuple_list ctx st
    | END_DATABASE -> C.end_tp ctx
    | _ -> failwith "expected NEW_EVENT|END_DATABASE"

  let rec srv_loop ctx st =
    match read_cmd st with
    | EOF -> send_eof ctx st
    | NEW_DATABASE ->
        let ts = Z.of_int64 (read_int64 st) in
        C.begin_tp ctx ts;
        read_tuple_list ctx st;
        srv_loop ctx st
    | LATENCY_MARKER ->
        let lm = read_int64 st in
        send_back_lm st lm;
        srv_loop ctx st
    | _ -> failwith "expected EOF|NEW_DATABASE|LATENCY_MARKER"

  let run_srv ctx schema inp outp =
    let st = ref { schema; inp; outp; num_events = 0 } in
    srv_loop ctx st

  let parse (schema : Db.schema) (sock_path : string) (ctx : C.t) =
    let addr = ADDR_UNIX sock_path in
    let sock = socket PF_UNIX SOCK_STREAM 0 in
    bind sock addr;
    listen sock 1;
    let fdpeer, _ = accept sock in
    let inp, outp = (in_channel_of_descr fdpeer, out_channel_of_descr fdpeer) in
    run_srv ctx schema inp outp;
    shutdown fdpeer SHUTDOWN_SEND;
    close_out outp;
    close sock;
    unlink sock_path;
    (try C.end_log ctx with Log_parser.Stop_parser -> ());
    true
end
