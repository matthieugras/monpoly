open MFOTL
open Db
open Predicate

val explicit_mon_output : bool ref

val write_explicitmon_state :
  Db.schema -> MFOTL.formula -> Predicate.var list -> unit
