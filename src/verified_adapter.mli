open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: Db.schema -> formula -> bool * (formula * string) option
val convert_db: monpolyData -> (string * Verified.Monitor.nat,
  Verified.Monitor.event_data option list Verified.Monitor.set list) Verified.Monitor.mapping *
  Verified.Monitor.nat
val convert_violations: (Verified.Monitor.nat * Verified.Monitor.event_data option list Verified.Monitor.set) list -> (int * relation) list
