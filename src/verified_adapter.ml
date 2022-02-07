open MFOTL
open Verified.Monitor
open Predicate
open Relation
open Helper
open Formula_serialize

exception UnsupportedFragment of string

let unsupported msg = raise (UnsupportedFragment msg)

let int_of_nat n = Z.to_int (integer_of_nat n)
let nat_of_int i = nat_of_integer (Z.of_int i)

let convert_tuple pname tl =
  let pos = ref 0 in
  List.map
    (fun t ->
      incr pos;
      Predicate.(
      Some (match t with
        | Int t -> EInt t
        | Str t -> EString t
        | Float t -> EFloat t
        | Regexp _ -> unsupported "Regular expressions constants are not supported"
      )))
    tl

type db = ((string * nat), (((event_data option) list) set list)) mapping

let empty_db = empty_db

let insert_into_db pname tl db =
  let a = nat_of_int (List.length tl) in
  insert_into_db (pname, a) (convert_tuple pname tl) db

type state =
  (((nat *
      (nat *
        (bool list *
          (bool list *
            ((nat * ((event_data option) list) set) queue *
              ((nat * ((event_data option) list) set) queue *
                (((event_data option) list) set *
                  (event_data wf_table *
                    ((((event_data option) list), nat) mapping *
                      (event_data wf_table *
                        (((event_data option) list), nat)
                          mapping)))))))))) *
     aggaux option),
    ((nat *
       (nat queue *
         ((((event_data option) list) set * (nat, nat) sum) queue *
           (nat *
             (bool list *
               (bool list *
                 (((event_data option) list) set *
                   ((((event_data option) list), nat) mapping *
                     ((nat, (((event_data option) list), (nat, nat) sum)
                              mapping)
                        mapping *
                       ((nat, nat) mapping *
                         (((event_data option) list) set list *
                           nat))))))))))) *
      aggaux option),
    unit)
    mstate_ext

let init cf = minit_safe cf

let cst_of_event_data = function
  | EInt x -> Int x
  | EFloat x -> Float x
  | EString x -> Str x

let unconvert_tuple l =
  List.filter_map (Option.map cst_of_event_data) l |> Tuple.make_tuple

let set_fold f s x = match s with
  | RBT_set r -> rbt_fold f r x
  | _ -> failwith "[set_fold] unexpected set representation"

let unconvert_violations =
  let add_tuple t = Relation.add (unconvert_tuple t) in
  let ucv_rel rel = set_fold add_tuple rel Relation.empty in
  let ucv (tp, (ts, v)) = (int_of_nat tp, integer_of_nat ts, ucv_rel v) in
  List.map ucv

let step t db st =
  let (vs, st') = mstep (db, nat_of_integer t) st in
  (unconvert_violations vs, st')

let is_monitorable dbschema f =
  let s = mmonitorable_exec (convert_formula dbschema f) in
  (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
