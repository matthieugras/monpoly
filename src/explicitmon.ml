open MFOTL
open Predicate
open Table
open String
open Map
open Set
open List

let explicit_mon_output = ref false
let curr_id = ref 0

module New_id(M: Map.S) = struct
  let maybe_make_new m key =
    match M.find_opt key m with
      Some id -> (m, id)
      | None -> (
        incr curr_id;
        (M.add key !curr_id m, !curr_id)
      )
end

module Str_int_pair = struct
    type t = string * int
    let compare = Stdlib.compare
end

module Pred_map =
  Map.Make(Str_int_pair)
module String_map = Map.Make(String)
module String_set = Set.Make(String)

type var_id = int
type pred_id = int

let rec fv_formula bound_vars = function
  | Equal (a,b)
  | Less (a,b)
  | LessEq (a,b) ->
      String_set.union (fv_trm bound_vars a) (fv_trm bound_vars b)
  | And (a,b)
  | Or (a,b)
  | Implies (a,b)
  | Equiv (a,b)
  | Since (_, a, b)
  | Until (_, a, b) -> String_set.union (fv_formula bound_vars a) (fv_formula bound_vars b)
  | Once (_, a)
  | Eventually (_, a)
  | Next (_, a)
  | Prev (_, a)
  | Neg a
  | Always (_, a) -> fv_formula bound_vars a
  | Exists (vl, a)
  | ForAll (vl, a) -> fv_formula (String_set.union (String_set.of_list vl) bound_vars) a
  | Pred (_, _, tl) ->
      List.fold_left (fun s t -> String_set.union s (fv_trm bound_vars t)) String_set.empty tl
  | _ -> failwith "unsupported operator"

and fv_trm bound_vars = function
  | Var a -> (
      if String_set.mem a bound_vars
      then String_set.empty
      else String_set.singleton a
    )
  | Cst _ -> String_set.empty
(* Unary terms *)
  | UMinus a
  | F2i a
  | I2f a -> fv_trm bound_vars a
(* Binary terms *)
  | Mult (a,b)
  | Div (a,b)
  | Mod (a,b)
  | Plus (a, b)
  | Minus (a, b) ->
      String_set.union (fv_trm bound_vars a) (fv_trm bound_vars b)
  | _ -> failwith "unsupported term"

type cst_type =
  | CstEq
  | CstLess
  | CstLessEq

type simple_op = 
  | AndAssign of term
  | AndRel of cst_type * term * term
  | Exists of var_id list

type predarg =
  | Var of tcst * var_id
  | Cst of cst

type exformula =
  | MPredicate of pred_id * (predarg list)
  | MTp of predarg
  | MTs of predarg
  | MTpTs of predarg * predarg
  | MAnd of exformula * exformula
  | MOr of exformula * exformula
  | MNeg of exformula
  | MPrev of interval * exformula
  | MNext of interval * exformula
  | MOnceB of interval * exformula
  | MOnceU of tsdiff
  | MSinceB of interval * exformula * exformula
  | MSinceU of tsdiff * exformula * exformula
  | FusedSimpleOp of simple_op list
  | MUntil of exformula * exformula
  | MEventually of exformula


let create_new_id =
  incr curr_id;
  !curr_id

let translate_pred_args schema_entry vmap terms =
  let vmap, ret, _ =
  List.fold_left (fun (vmap, trsfd, idx) t -> 
    match t with
      Predicate.Var name -> (
        let module S = New_id(String_map) in
        let (vmap, new_id) = S.maybe_make_new vmap name in
          let ty = snd (nth schema_entry idx) in
          let trsfd = (Var (ty, new_id)) :: trsfd in
          (vmap, trsfd, idx + 1)
      )
    | Predicate.Cst cst ->
        (vmap, (Cst cst) :: trsfd, idx + 1)
    | _ -> failwith "unsupported predicate arg"
  ) (vmap, [], 0) terms in
  vmap, List.rev ret

let translate_pred name arity terms schema pmap vmap =
  let module P = New_id(Pred_map) in
  let pmap, new_id = P.maybe_make_new pmap (name, arity) in
  let vmap, trsfd = translate_pred_args (List.assoc name schema) vmap terms in
  let generic_pred =
    if name == "tp" && arity == 1 then
      MTp (nth trsfd 0)
    else if name = "ts" && arity == 1 then
      MTs (nth trsfd 0)
    else if name = "tpts" && arity == 2 then
      MTpTs (nth trsfd 0, nth trsfd 1)
    else
      MPredicate (new_id, trsfd)
  in
  generic_pred, pmap, vmap

let rec translate_formula schema pmap vmap = function
  (* rewriting cases *)
  | ForAll (v,f) -> translate_formula schema pmap vmap (Neg (Exists (v, (Neg f))))
  | Equiv (a,b) -> translate_formula schema pmap vmap (And ((Implies (a,b)), (Implies (a,b))))
  | Implies (a,b) -> translate_formula schema pmap vmap (Or ((Neg a), b))
  | Always (intv, a) -> translate_formula schema pmap vmap (Neg (Eventually (intv, Neg a)))
  | Pred (name, arity, terms) -> translate_pred name arity terms schema pmap vmap
  | _ -> failwith "rofl"

let make_exformula schema f = 
  let (f, pmap, _) = translate_formula schema (Pred_map.empty) (String_map.empty) f in
  "rofl"
