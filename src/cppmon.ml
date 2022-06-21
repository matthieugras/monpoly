open MFOTL
open Predicate
open Relation
open Helper

module MyZ = struct
  include Z

  let yojson_of_t arg = yojson_of_int (Z.to_int arg)
  let t_of_yojson arg = Z.of_int (int_of_yojson arg)
end

exception UnsupportedFragment of string

let unsupported msg = raise (UnsupportedFragment msg)

type nat = Nat of MyZ.t [@@deriving yojson]

type event_data = EInt of MyZ.t | EFloat of float | EString of string
[@@deriving yojson]

type trm =
  | Var of nat
  | Const of event_data
  | Plus of trm * trm
  | Minus of trm * trm
  | UMinus of trm
  | Mult of trm * trm
  | Div of trm * trm
  | Mod of trm * trm
  | F2i of trm
  | I2f of trm
[@@deriving yojson]

type enat = Enat of nat | Infinity_enat [@@deriving yojson]

type agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
[@@deriving yojson]

type interval = nat * enat [@@deriving yojson]

type formula =
  | Pred of string * trm list
  | Let of string * formula * formula
  | LetPast of string * formula * formula
  | Eq of trm * trm
  | Less of trm * trm
  | LessEq of trm * trm
  | Neg of formula
  | Or of formula * formula
  | And of formula * formula
  | Ands of formula list
  | Exists of formula
  | Agg of nat * (agg_type * event_data) * nat * trm * formula
  | Prev of interval * formula
  | Next of interval * formula
  | Since of formula * interval * formula
  | Until of formula * interval * formula
  | TP of trm
  | TS of trm
  | TPTS of trm * trm
[@@deriving yojson]

let nat_of_int arg = Nat (MyZ.of_int arg)
let my_enat_of_int arg = Enat (Nat arg)
let my_nat_of_integer arg = Nat arg

let convert_cst = function
  | Int x -> EInt x
  | Str x -> EString x
  | Float x -> EFloat x
  | Regexp _ -> unsupported "Regular expression constant are not supported"

let convert_var fvl bvl a =
  nat_of_int
    (try Misc.get_pos a bvl
     with Not_found -> (
       List.length bvl
       + try Misc.get_pos a fvl with Not_found -> List.length fvl))

let convert_term fvl bvl =
  let rec convert = function
    | Cst c -> Const (convert_cst c)
    | Var a -> Var (convert_var fvl bvl a)
    | F2i t -> F2i (convert t)
    | I2f t -> I2f (convert t)
    | Plus (t1, t2) -> Plus (convert t1, convert t2)
    | Minus (t1, t2) -> Minus (convert t1, convert t2)
    | UMinus t -> UMinus (convert t)
    | Mult (t1, t2) -> Mult (convert t1, convert t2)
    | Div (t1, t2) -> Div (convert t1, convert t2)
    | Mod (t1, t2) -> Mod (convert t1, convert t2)
    | t -> unsupported ("Unsupported term " ^ string_of_term t)
  in
  convert

let convert_interval (l, r) =
  let lm =
    match l with
    | OBnd a -> MyZ.(a + one)
    | CBnd a -> a
    | Inf -> unsupported ("Unsupported interval " ^ string_of_interval (l, r))
  in
  let um =
    match r with OBnd a -> Some MyZ.(a - one) | CBnd a -> Some a | Inf -> None
  in
  match um with
  | None -> (my_nat_of_integer lm, Infinity_enat)
  | Some um ->
      if lm <= um then (my_nat_of_integer lm, my_enat_of_int um)
      else unsupported ("Unsupported interval " ^ string_of_interval (l, r))

let convert_agg_op = function
  | Cnt -> Agg_Cnt
  | Min -> Agg_Min
  | Max -> Agg_Max
  | Sum -> Agg_Sum
  | Avg -> Agg_Avg
  | Med -> Agg_Med

let special_predicates = [ "tp"; "ts"; "tpts" ]

let convert_special_predicate1 fvl bvl = function
  | "tp", _, [ t ] -> TP (convert_term fvl bvl t)
  | "ts", _, [ t ] -> TS (convert_term fvl bvl t)
  | "tpts", _, [ t1; t2 ] ->
      TPTS (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | _ -> failwith "[convert_special_predicate1] internal error"

let convert_formula_serialize f =
  let free_vars = MFOTL.free_vars f in
  let truth = Equal (Cst (Int Z.zero), Cst (Int Z.zero)) in
  let rec createExists n f =
    match n with 0 -> f | n -> createExists (n - 1) (Exists f)
  in
  let rec convert_formula_vars fvl bvl lets = function
    | Equal (t1, t2) -> Eq (convert_term fvl bvl t1, convert_term fvl bvl t2)
    | Less (t1, t2) -> Less (convert_term fvl bvl t1, convert_term fvl bvl t2)
    | LessEq (t1, t2) ->
        LessEq (convert_term fvl bvl t1, convert_term fvl bvl t2)
    | Pred p ->
        let n, a, tl = p in
        if List.mem n special_predicates && not (List.mem (n, a) lets) then
          convert_special_predicate1 fvl bvl p
        else Pred (n, List.map (convert_term fvl bvl) tl)
    | Let (p, f1, f2) ->
        let n, a, ts = Predicate.get_info p in
        let fvl1 = List.flatten (List.map Predicate.tvars ts) in
        let lets2 = (n, a) :: lets in
        Let
          ( n,
            convert_formula_vars fvl1 [] lets f1,
            convert_formula_vars fvl bvl lets2 f2 )
    | LetPast (p, f1, f2) ->
        let n, a, ts = Predicate.get_info p in
        let fvl1 = List.flatten (List.map Predicate.tvars ts) in
        let lets' = (n, a) :: lets in
        LetPast
          ( n,
            convert_formula_vars fvl1 [] lets' f1,
            convert_formula_vars fvl bvl lets' f2 )
    | Neg f -> Neg (convert_formula_vars fvl bvl lets f)
    | And (f1, f2) ->
        And
          ( convert_formula_vars fvl bvl lets f1,
            convert_formula_vars fvl bvl lets f2 )
    | Or (f1, f2) ->
        Or
          ( convert_formula_vars fvl bvl lets f1,
            convert_formula_vars fvl bvl lets f2 )
    | Implies (f1, f2) -> convert_formula_vars fvl bvl lets (Or (Neg f1, f2))
    | Equiv (f1, f2) ->
        convert_formula_vars fvl bvl lets
          (And (Implies (f1, f2), Implies (f2, f2)))
    | Exists (v, f) ->
        createExists (List.length v) (convert_formula_vars fvl (v @ bvl) lets f)
    | ForAll (v, f) ->
        convert_formula_vars fvl bvl lets (Neg (Exists (v, Neg f)))
    | Aggreg (t_y, y, op, x, glist, f) ->
        let t_y =
          match t_y with TCst a -> a | _ -> failwith "Internal error"
        in
        let attr = MFOTL.free_vars f in
        let bound = Misc.diff attr glist in
        let bvl_f = bound @ bvl in
        Agg
          ( convert_var fvl bvl y,
            (convert_agg_op op, convert_cst (aggreg_default_value op t_y)),
            nat_of_int (List.length bound),
            convert_term fvl bvl_f (Var x),
            convert_formula_vars fvl bvl_f lets f )
    | Prev (intv, f) ->
        Prev (convert_interval intv, convert_formula_vars fvl bvl lets f)
    | Next (intv, f) ->
        Next (convert_interval intv, convert_formula_vars fvl bvl lets f)
    | Since (intv, f1, f2) ->
        Since
          ( convert_formula_vars fvl bvl lets f1,
            convert_interval intv,
            convert_formula_vars fvl bvl lets f2 )
    | Until (intv, f1, f2) ->
        Until
          ( convert_formula_vars fvl bvl lets f1,
            convert_interval intv,
            convert_formula_vars fvl bvl lets f2 )
    | Eventually (intv, f) ->
        convert_formula_vars fvl bvl lets (Until (intv, truth, f))
    | Once (intv, f) ->
        convert_formula_vars fvl bvl lets (Since (intv, truth, f))
    | Always (intv, f) ->
        convert_formula_vars fvl bvl lets (Neg (Eventually (intv, Neg f)))
    | PastAlways (intv, f) ->
        convert_formula_vars fvl bvl lets (Neg (Once (intv, Neg f)))
    | f -> unsupported (string_of_formula "Unsupported formula " f)
  in
  convert_formula_vars free_vars [] [] f

let output_cppmon = ref false

let print_cppmon_formula f pp =
  let f = convert_formula_serialize f in
  let f = yojson_of_formula f in
  let f =
    if pp then Yojson.Safe.pretty_to_string f else Yojson.Safe.to_string f
  in
  Printf.printf "%s" f
