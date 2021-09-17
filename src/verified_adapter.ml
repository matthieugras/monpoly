open MFOTL
open Verified.Monitor
open Predicate
open Relation
open Helper
open Formula_serialize

exception UnsupportedFragment of string

let (<<) f g x = f(g(x))
let nat_of_int = nat_of_integer << Z.of_int
let nat_of_float = nat_of_integer << Z.of_float
let int_of_nat = Z.to_int << integer_of_nat (* Problem? *)
let int_of_enat = function
  | Enat n -> Z.to_int (integer_of_nat n)
  | Infinity_enat -> failwith "[int_of_enat] internal error"

let deoptionalize  =
  let is_some = function Some _ -> true | _ -> false in
  List.map (function | Some x -> x | None -> assert false) << List.filter (is_some)

let convert_cst = function
  | Int x -> EInt (Z.of_int x)
  | Str x -> EString x
  | Float x -> EFloat x
  | ZInt x -> EInt x

let convert_db md =
  let rbt_single x = RBT_set (rbt_insert x rbt_empty) in
  let convert_cst' x = Some (convert_cst x) in
  let add_builtin xs (name, tup) =
    let arity = nat_of_int (List.length tup) in
    ((name, arity), rbt_single (List.map convert_cst' tup)) :: xs
  in
  let convert_table t =
    let (name, attrs) = (Table.get_schema t) in
    let arity = nat_of_int (List.length attrs) in
    ((name, arity), RBT_set (Relation.fold
      (fun v -> rbt_insert (List.map convert_cst' v))
      (Table.get_relation t) rbt_empty))
  in
  let db_events = List.map convert_table (Db.get_tables md.db) in
  let all_events = List.fold_left add_builtin db_events
    ["tp", [Int md.tp]; "ts", [Float md.ts]; "tpts", [Int md.tp; Float md.ts]]
  in
  (mk_db all_events, nat_of_float md.ts)

let cst_of_event_data = function
  | EInt x -> (try Int (Z.to_int x) with Z.Overflow -> ZInt x)
  | EFloat x -> Float x
  | EString x -> Str x

let convert_tuple xs = Tuple.make_tuple (List.map cst_of_event_data (deoptionalize xs))

(* (Verified.nat * Verified.event_data option list Verified.set) list -> (int * relation) list *)
let convert_violations =
  List.map (fun (tp, rbt) ->
  let v = match rbt with
    | RBT_set r -> r
    | _ -> failwith "Impossible!" in
    ((int_of_nat tp),
     Relation.make_relation
      (rbt_fold (fun t l -> (convert_tuple t) :: l) v [] )))

let is_monitorable dbschema f =
  let s = (mmonitorable_exec << convert_formula dbschema) f in
  (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
