open Formula_serialize

let no_mw = ref false
let dump_to_json = ref false

module Monitor = struct
  type t = {
    fv_pos: int list;
    mutable cur_tp: int;
    mutable cur_ts: MFOTL.timestamp;
    mutable cur_db: Verified_adapter.db;
    mutable cur_state: Verified_adapter.state;
  }

  let begin_tp ctxt ts =
    if ts >= ctxt.cur_ts then
      ctxt.cur_ts <- ts
    else
      begin
        Printf.eprintf "Error: Out of order timestamp %s (previous: %s)\n"
          (MFOTL.string_of_ts ts) (MFOTL.string_of_ts ctxt.cur_ts);
        exit 1
      end

  let tuple ctxt s tl =
    ctxt.cur_db <- Verified_adapter.insert_into_db s tl ctxt.cur_db

  let end_tp ctxt =
    let db = ctxt.cur_db in
    ctxt.cur_db <- Verified_adapter.empty_db;
    let (vs, new_state) = Verified_adapter.step ctxt.cur_ts db ctxt.cur_state in
    ctxt.cur_state <- new_state;
    if !Misc.verbose then
      Printf.printf "At time point %d:\n%!" ctxt.cur_tp;
    List.iter (fun (q, tsq, rel) ->
      Helper.show_results ctxt.fv_pos ctxt.cur_tp q tsq rel;
      if !Misc.stop_at_first_viol && not (Relation.is_empty rel) then
        raise Log_parser.Stop_parser
      ) vs;
    ctxt.cur_tp <- ctxt.cur_tp + 1

  let command ctxt _name _params =
    prerr_endline "Error: Commands are not supported by the verified kernel";
    if not !Misc.ignore_parse_errors then exit 1

  let end_log ctxt =
    if !Misc.new_last_ts then
      begin
        begin_tp ctxt MFOTL.ts_max;
        end_tp ctxt
      end

  let parse_error ctxt pos msg =
    prerr_endline "Error while parsing log:";
    prerr_endline (Log_parser.string_of_position pos ^ ": " ^ msg);
    if not !Misc.ignore_parse_errors then exit 1
end

module P = Log_parser.Make (Monitor)
module S = Socket_input.Make (Monitor)

let dump_formula dbschema f =
  let sf = convert_formula_serialize dbschema f in
  let json = yojson_of_formula sf in
  let str_json_pretty = Yojson.Safe.pretty_to_string json in
  (*let str_json_compact = Yojson.Safe.to_string json in *)
  Printf.printf "%s\n" str_json_pretty;
  (*Printf.printf "Pretty:\n%s\n\nCompact:\n%s\n" str_json_pretty str_json_compact;*)
  exit 0

let monitor dbschema logfile fv f =
  (* compute permutation for output tuples *)
  let fv_pos = List.map snd (Table.get_matches (MFOTL.free_vars f) fv) in
  assert (List.length fv_pos = List.length fv);
  if !dump_to_json then
    dump_formula dbschema f;
  let cf = Formula_serialize.convert_formula dbschema f in
  let cf = if !no_mw then cf else Verified.Monitor.convert_multiway cf in
  let ctxt = Monitor.{
    fv_pos;
    cur_tp = 0;
    cur_ts = MFOTL.ts_invalid;
    cur_db = Verified_adapter.empty_db;
    cur_state = Verified_adapter.init cf;
  } in
  if !Misc.socket_input then
    ignore (P.parse_file dbschema logfile ctxt)
  else
    ignore (S.parse ctxt dbschema "cppmon")
