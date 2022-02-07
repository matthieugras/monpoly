open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: Db.schema -> formula -> bool * (formula * string) option

type db
val empty_db: db
val insert_into_db: var -> Tuple.tuple -> db -> db

type state
val init: Verified.Monitor.formula -> state
val step: MFOTL.timestamp -> db -> state -> (int * MFOTL.timestamp * relation) list * state
