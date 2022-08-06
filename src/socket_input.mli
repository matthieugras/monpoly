module type Consumer = sig
  type t

  val begin_tp : t -> MFOTL.timestamp -> unit
  val tuple : t -> Table.schema -> string list -> unit
  val end_tp : t -> unit
  val command : t -> string -> Helper.commandParameter option -> unit
  val end_log : t -> unit
  val parse_error : t -> Lexing.position -> string -> unit
end

module Make(C: Consumer): sig
  val parse:  Db.schema -> string -> C.t -> bool
end
