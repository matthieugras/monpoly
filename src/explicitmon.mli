open MFOTL
open Table

val explicit_mon_output: bool ref

val make_exformula: (Table.schema -> MFOTL.formula -> string)
