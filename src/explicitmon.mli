open MFOTL
open Db

val explicit_mon_output: bool ref
val write_explicitmon_state: Db.schema -> MFOTL.formula -> unit
