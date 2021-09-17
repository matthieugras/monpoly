open MFOTL
open Predicate
open Relation
open Helper
open Verified.Monitor

type formula
val yojson_of_formula: formula -> Yojson.Safe.t
val convert_formula: Db.schema -> MFOTL.formula -> Verified.Monitor.formula
val convert_formula_serialize: Db.schema -> MFOTL.formula -> formula
val serial_to_verified_formula: formula -> Verified.Monitor.formula