open MFOTL
open Predicate
open Relation
open Helper
open Verified.Monitor

module Z = struct
  include Z

  let yojson_of_t arg = yojson_of_int (Z.to_int arg)
end

exception UnsupportedFragment of string

type nat = Nat of Z.t [@@deriving yojson_of]

type event_data = EInt of Z.t | EFloat of float | EString of string
[@@deriving yojson_of]

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
[@@deriving yojson_of]

type enat = Enat of nat | Infinity_enat [@@deriving yojson_of]

type agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
[@@deriving yojson_of]

type interval = nat * enat [@@deriving yojson_of]

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
  | MatchF of interval * regex
  | MatchP of interval * regex
[@@deriving yojson_of]

and regex =
  | Skip of nat
  | Test of formula
  | Plusa of regex * regex
  | Times of regex * regex
  | Star of regex
[@@deriving yojson_of]

let ( << ) f g x = f (g x)

let nat_of_int arg = Nat (Z.of_int arg)

let nat_of_float arg = Nat (Z.of_float arg)

let enat_of_float f = Enat (Nat (Z.of_float f))

let filterWith f p = List.map f << List.filter p

let deoptionalize =
  let is_some = function Some _ -> true | _ -> false in
  List.map (function Some x -> x | None -> assert false)
  << List.filter is_some

let index_of =
  let rec index_of_rec c x lst =
    match lst with
    | [] -> raise (Failure "Not Found")
    | hd :: tl -> if hd = x then c else index_of_rec (c + 1) x tl
  in
  index_of_rec 0

let cst_to_verified : event_data -> Verified.Monitor.event_data = function
  | EInt x -> EInt x
  | EFloat x -> EFloat x
  | EString x -> EString x

let nat_to_verified : nat -> Verified.Monitor.nat = function
  | Nat t -> nat_of_integer t

let enat_to_verified : enat -> Verified.Monitor.enat = function
  | Infinity_enat -> Infinity_enat
  | Enat n -> Enat (nat_to_verified n)

let rec trm_to_verified : trm -> Verified.Monitor.trm = function
  | Var x -> Var (nat_to_verified x)
  | Const x -> Const (cst_to_verified x)
  | Plus (x1, x2) -> Plus (trm_to_verified x1, trm_to_verified x2)
  | Minus (x1, x2) -> Minus (trm_to_verified x1, trm_to_verified x2)
  | UMinus x -> UMinus (trm_to_verified x)
  | Mult (x1, x2) -> Mult (trm_to_verified x1, trm_to_verified x2)
  | Div (x1, x2) -> Div (trm_to_verified x1, trm_to_verified x2)
  | Mod (x1, x2) -> Mod (trm_to_verified x1, trm_to_verified x2)
  | F2i x -> F2i (trm_to_verified x)
  | I2f x -> I2f (trm_to_verified x)

let interval_to_verified (l : nat) (u : enat) =
  interval (nat_to_verified l) (enat_to_verified u)

let agg_type_to_verified : agg_type -> Verified.Monitor.agg_type = function
  | Agg_Cnt -> Agg_Cnt
  | Agg_Min -> Agg_Min
  | Agg_Max -> Agg_Max
  | Agg_Sum -> Agg_Sum
  | Agg_Avg -> Agg_Avg
  | Agg_Med -> Agg_Med

let rec formula_to_verified : formula -> Verified.Monitor.formula = function
  | Pred (x1, x2) -> Pred (x1, List.map trm_to_verified x2)
  | Let (x1, x2, x3) -> Let (x1, formula_to_verified x2, formula_to_verified x3)
  | LetPast (x1, x2, x3) ->
      LetPast (x1, formula_to_verified x2, formula_to_verified x3)
  | Eq (x1, x2) -> Eq (trm_to_verified x1, trm_to_verified x2)
  | Less (x1, x2) -> Less (trm_to_verified x1, trm_to_verified x2)
  | LessEq (x1, x2) -> LessEq (trm_to_verified x1, trm_to_verified x2)
  | Neg x -> Neg (formula_to_verified x)
  | And (x1, x2) -> And (formula_to_verified x1, formula_to_verified x2)
  | Or (x1, x2) -> Or (formula_to_verified x1, formula_to_verified x2)
  | Ands x -> Ands (List.map formula_to_verified x)
  | Exists x -> Exists (formula_to_verified x)
  | Prev ((x1, x2), x3) ->
      Prev (interval_to_verified x1 x2, formula_to_verified x3)
  | Next ((x1, x2), x3) ->
      Next (interval_to_verified x1 x2, formula_to_verified x3)
  | Since (x1, (x2, x3), x4) ->
      Since
        ( formula_to_verified x1,
          interval_to_verified x2 x3,
          formula_to_verified x4 )
  | Until (x1, (x2, x3), x4) ->
      Until
        ( formula_to_verified x1,
          interval_to_verified x2 x3,
          formula_to_verified x4 )
  | MatchF ((x1, x2), x3) ->
      MatchF (interval_to_verified x1 x2, regex_to_verified x3)
  | MatchP ((x1, x2), x3) ->
      MatchP (interval_to_verified x1 x2, regex_to_verified x3)
  | Agg (x1, (x2, x3), x4, x5, x6) ->
      Agg
        ( nat_to_verified x1,
          (agg_type_to_verified x2, cst_to_verified x3),
          nat_to_verified x4,
          trm_to_verified x5,
          formula_to_verified x6 )

and regex_to_verified : regex -> Verified.Monitor.formula Verified.Monitor.regex
    = function
  | Skip x -> Skip (nat_to_verified x)
  | Test x -> Test (formula_to_verified x)
  | Plusa (x1, x2) -> Plusa (regex_to_verified x1, regex_to_verified x2)
  | Times (x1, x2) -> Times (regex_to_verified x1, regex_to_verified x2)
  | Star x -> Star (regex_to_verified x)

let convert_cst = function
  | Int x -> EInt (Z.of_int x)
  | Str x -> EString x
  | Float x -> EFloat x
  | ZInt x -> EInt x

let convert_var fvl bvl a =
  nat_of_int
    (try index_of a bvl
     with Failure s -> (
       List.length bvl + try index_of a fvl with Failure s -> List.length fvl))

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
    | _ -> failwith "[convert_term] unsupported term"
  in
  convert

let convert_interval (l, r) =
  let lm =
    match l with
    | OBnd a -> a +. 1.
    | CBnd a -> a
    | Inf ->
        let msg = "Unsupported interval " ^ string_of_interval (l, r) in
        raise (UnsupportedFragment msg)
  in
  let um =
    match r with OBnd a -> Some (a -. 1.) | CBnd a -> Some a | Inf -> None
  in
  match um with
  | None -> (nat_of_float lm, Infinity_enat)
  | Some um ->
      if lm <= um then (nat_of_float lm, enat_of_float um)
      else
        let msg = "Unsupported interval " ^ string_of_interval (l, r) in
        raise (UnsupportedFragment msg)

let convert_agg_op = function
  | Cnt -> Agg_Cnt
  | Min -> Agg_Min
  | Max -> Agg_Max
  | Sum -> Agg_Sum
  | Avg -> Agg_Avg
  | Med -> Agg_Med

let serial_to_verified_formula = formula_to_verified

let convert_formula_serialize (dbschema : Db.schema) f =
  let free_vars = MFOTL.free_vars f in
  let truth = Equal (Cst (Int 0), Cst (Int 0)) in
  let rec createExists n f =
    match n with 0 -> f | n -> createExists (n - 1) (Exists f)
  in
  let rec convert_formula_vars fvl bvl = function
    | Equal (t1, t2) -> Eq (convert_term fvl bvl t1, convert_term fvl bvl t2)
    | Less (t1, t2) -> Less (convert_term fvl bvl t1, convert_term fvl bvl t2)
    | LessEq (t1, t2) ->
        LessEq (convert_term fvl bvl t1, convert_term fvl bvl t2)
    | Pred (p, _, tl) -> Pred (p, List.map (fun t -> convert_term fvl bvl t) tl)
    | Let (p, f1, f2) ->
        let n, a, ts = Predicate.get_info p in
        let fvl1 = List.flatten (List.map Predicate.tvars ts) in
        Let (n, convert_formula_vars fvl1 [] f1, convert_formula_vars fvl bvl f2)
    | LetPast (p, f1, f2) ->
        let n, a, ts = Predicate.get_info p in
        let fvl1 = List.flatten (List.map Predicate.tvars ts) in
        LetPast
          (n, convert_formula_vars fvl1 [] f1, convert_formula_vars fvl bvl f2)
    | Neg f -> Neg (convert_formula_vars fvl bvl f)
    | And (f1, f2) ->
        And (convert_formula_vars fvl bvl f1, convert_formula_vars fvl bvl f2)
    | Or (f1, f2) ->
        Or (convert_formula_vars fvl bvl f1, convert_formula_vars fvl bvl f2)
    | Implies (f1, f2) -> convert_formula_vars fvl bvl (Or (Neg f1, f2))
    | Equiv (f1, f2) ->
        convert_formula_vars fvl bvl (And (Implies (f1, f2), Implies (f2, f2)))
    | Exists (v, f) ->
        createExists (List.length v) (convert_formula_vars fvl (v @ bvl) f)
    | ForAll (v, f) -> convert_formula_vars fvl bvl (Neg (Exists (v, Neg f)))
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
            convert_formula_vars fvl bvl_f f )
    | Prev (intv, f) ->
        Prev (convert_interval intv, convert_formula_vars fvl bvl f)
    | Next (intv, f) ->
        Next (convert_interval intv, convert_formula_vars fvl bvl f)
    | Since (intv, f1, f2) ->
        Since
          ( convert_formula_vars fvl bvl f1,
            convert_interval intv,
            convert_formula_vars fvl bvl f2 )
    | Until (intv, f1, f2) ->
        Until
          ( convert_formula_vars fvl bvl f1,
            convert_interval intv,
            convert_formula_vars fvl bvl f2 )
    | Eventually (intv, f) ->
        convert_formula_vars fvl bvl (Until (intv, truth, f))
    | Once (intv, f) -> convert_formula_vars fvl bvl (Since (intv, truth, f))
    | Always (intv, f) ->
        convert_formula_vars fvl bvl (Neg (Eventually (intv, Neg f)))
    | PastAlways (intv, f) ->
        convert_formula_vars fvl bvl (Neg (Once (intv, Neg f)))
    | Frex (intv, r) -> MatchF (convert_interval intv, convert_re_vars fvl bvl r)
    | Prex (intv, r) -> MatchP (convert_interval intv, convert_re_vars fvl bvl r)
    | _ -> failwith "[convert_term] unsupported formula"
  and convert_re_vars fvl bvl = function
    | Wild -> Skip (Nat (Z.of_int 1))
    | Test f -> Test (convert_formula_vars fvl bvl f)
    | Concat (r1, r2) ->
        Times (convert_re_vars fvl bvl r1, convert_re_vars fvl bvl r2)
    | Plus (r1, r2) ->
        Plusa (convert_re_vars fvl bvl r1, convert_re_vars fvl bvl r2)
    | Star r -> Star (convert_re_vars fvl bvl r)
  in
  convert_formula_vars free_vars [] f

let convert_formula (dbschema : Db.schema) (f : MFOTL.formula) =
  serial_to_verified_formula (convert_formula_serialize dbschema f)