open MFOTL
open Predicate
open Table
open String
open Map
open Set
open List
open Db

let explicit_mon_output = ref false
let curr_id = ref 0

module New_id (M : Map.S) = struct
  include M

  let maybe_make_new m key =
    match M.find_opt key m with
    | Some id -> (m, id)
    | None ->
        incr curr_id;
        (M.add key !curr_id m, !curr_id)

  let make_new m key =
    incr curr_id;
    let old_id = M.find_opt key m in
    (M.update key (fun _ -> Some !curr_id) m, old_id, !curr_id)

  let make_new_mult m keys =
    let m, old_ids, new_ids =
      List.fold_left
        (fun (m, old_ids, new_ids) key ->
          let m, old_id, new_id = make_new m key in
          (m, old_id :: old_ids, new_id :: new_ids))
        (m, [], []) keys
    in
    (m, List.rev old_ids, List.rev new_ids)

  let update_all m a b =
    List.fold_left
      (fun m (a, b) -> M.update a (fun _ -> b) m)
      m (List.combine a b)
end

module Str_int_pair = struct
  type t = string * int

  let compare = Stdlib.compare
end

module Pred_map = New_id (Map.Make (Str_int_pair))
module Var_map = New_id (Map.Make (String))
module String_set = Set.Make (String)

type var_id = int
type pred_id = int

type translation_ctx = {
  schema : Db.schema;
  pmap : pred_id Pred_map.t;
  vmap : var_id Var_map.t;
}

let rec fv_formula bound_vars = function
  | Equal (a, b) | Less (a, b) | LessEq (a, b) ->
      String_set.union (fv_trm bound_vars a) (fv_trm bound_vars b)
  | And (a, b)
  | Or (a, b)
  | Implies (a, b)
  | Equiv (a, b)
  | Since (_, a, b)
  | Until (_, a, b) ->
      String_set.union (fv_formula bound_vars a) (fv_formula bound_vars b)
  | Once (_, a)
  | Eventually (_, a)
  | Next (_, a)
  | Prev (_, a)
  | Neg a
  | Always (_, a) ->
      fv_formula bound_vars a
  | Exists (vl, a) | ForAll (vl, a) ->
      fv_formula (String_set.union (String_set.of_list vl) bound_vars) a
  | Pred (_, _, tl) ->
      List.fold_left
        (fun s t -> String_set.union s (fv_trm bound_vars t))
        String_set.empty tl
  | _ -> failwith "unsupported operator"

and fv_trm bound_vars = function
  | Var a ->
      if String_set.mem a bound_vars then String_set.empty
      else String_set.singleton a
  | Cst _ -> String_set.empty
  | UMinus a | F2i a | I2f a -> fv_trm bound_vars a
  | Mult (a, b) | Div (a, b) | Mod (a, b) | Plus (a, b) | Minus (a, b) ->
      String_set.union (fv_trm bound_vars a) (fv_trm bound_vars b)
  | _ -> failwith "unsupported term"

type cst_type = CstEq | CstLess | CstLessEq

type simple_op =
  | MAndAssign of term
  | MAndRel of cst_type * term * term
  | MExists of var_id list

type predarg = Var of tcst * var_id | Cst of cst
type bound = Bnd of tsdiff | Inf
type interval = bound * bound

let translate_bnd = function
  | OBnd a -> Bnd (MFOTL.ts_minus a Z.one)
  | CBnd a -> Bnd a
  | MFOTL.Inf -> Inf

let translate_intv (a, b) = (translate_bnd a, translate_bnd b)
let is_inf_intv = function _, Inf -> true | _ -> false

let if_unbounded = function
  | Bnd a, Inf -> Some a
  | Bnd a, Bnd b -> None
  | _ -> failwith "malformed"

type exformula =
  | MPredicate of pred_id * predarg list
  | MTp of predarg
  | MTs of predarg
  | MTpts of predarg * predarg
  | MAnd of exformula * exformula
  | MOr of exformula * exformula
  | MNeg of exformula
  | MPrev of interval * exformula
  | MNext of interval * exformula
  | MOnceB of interval * exformula
  | MOnceU of tsdiff * exformula
  | MSinceB of interval * exformula * exformula
  | MSinceU of tsdiff * exformula * exformula
  | MFusedSimpleOp of simple_op list * exformula
  | MUntil of interval * exformula * exformula
  | MEventually of interval * exformula

let create_new_id =
  incr curr_id;
  !curr_id

let translate_pred_args schema_entry vmap terms =
  let vmap, ret, _ =
    List.fold_left
      (fun (vmap, trsfd, idx) t ->
        match t with
        | Predicate.Var name ->
            let vmap, new_id = Var_map.maybe_make_new vmap name in
            let ty = snd (nth schema_entry idx) in
            let trsfd = Var (ty, new_id) :: trsfd in
            (vmap, trsfd, idx + 1)
        | Predicate.Cst cst -> (vmap, Cst cst :: trsfd, idx + 1)
        | _ -> failwith "unsupported predicate arg")
      (vmap, [], 0) terms
  in
  (vmap, List.rev ret)

let translate_pred ctx name arity terms =
  let pmap, new_id = Pred_map.maybe_make_new ctx.pmap (name, arity) in
  let vmap, trsfd =
    translate_pred_args (List.assoc name ctx.schema) ctx.vmap terms
  in
  let generic_pred =
    if name == "tp" && arity == 1 then MTp (nth trsfd 0)
    else if name = "ts" && arity == 1 then MTs (nth trsfd 0)
    else if name = "tpts" && arity == 2 then MTpts (nth trsfd 0, nth trsfd 1)
    else MPredicate (new_id, trsfd)
  in
  (generic_pred, { ctx with pmap; vmap })

let rec translate_formula ctx = function
  (* rewriting cases *)
  | ForAll (v, f) -> translate_formula ctx (Neg (Exists (v, Neg f)))
  | Equiv (a, b) -> translate_formula ctx (And (Implies (a, b), Implies (a, b)))
  | Implies (a, b) -> translate_formula ctx (Or (Neg a, b))
  | Always (intv, a) -> translate_formula ctx (Neg (Eventually (intv, Neg a)))
  | PastAlways (intv, a) -> translate_formula ctx (Neg (Once (intv, Neg a)))
  (* other cases *)
  | Pred (name, arity, terms) -> translate_pred ctx name arity terms
  | Prev (intv, f) ->
      let f, ctx = translate_formula ctx f in
      let intv = translate_intv intv in
      (MPrev (intv, f), ctx)
  | Next (intv, f) ->
      let f, ctx = translate_formula ctx f in
      let intv = translate_intv intv in
      (MNext (intv, f), ctx)
  | Once (intv, f) ->
      let f, ctx = translate_formula ctx f in
      let intv = translate_intv intv in
      let f =
        match if_unbounded intv with
        | Some k -> MOnceU (k, f)
        | None -> MOnceB (intv, f)
      in
      (f, ctx)
  | Eventually (intv, f) ->
      let f, ctx = translate_formula ctx f in
      let intv = translate_intv intv in
      (MEventually (intv, f), ctx)
  | Since (intv, f1, f2) ->
      let f1, ctx = translate_formula ctx f1 in
      let f2, ctx = translate_formula ctx f2 in
      let intv = translate_intv intv in
      let f =
        match if_unbounded intv with
        | Some k -> MSinceU (k, f1, f2)
        | None -> MSinceB (intv, f1, f2)
      in
      (f, ctx)
  | Until (intv, f1, f2) ->
      let f1, ctx = translate_formula ctx f1 in
      let f2, ctx = translate_formula ctx f2 in
      (MUntil (translate_intv intv, f1, f2), ctx)
  | Or (f1, f2) ->
      let f1, ctx = translate_formula ctx f1 in
      let f2, ctx = translate_formula ctx f2 in
      (MOr (f1, f2), ctx)
  | Exists (_, _) as f -> transform_fused_op ctx [] f
  | And (_, _) as f ->
      (* possibly a fused op *)
      transform_fused_op ctx [] f
  | _ -> failwith "unsupported fragment"

and transform_fused_op ctx sops = function
  | Exists (vars, f) ->
      let vmap, old_ids, new_ids = Var_map.make_new_mult ctx.vmap vars in
      let f, ctx =
        transform_fused_op { ctx with vmap } (MExists new_ids :: sops) f
      in
      let vmap = Var_map.update_all vmap vars old_ids in
      (f, { ctx with vmap })
  | And (f1, f2) -> failwith "rofl"
  | f ->
      let f, ctx = translate_formula ctx f in
      (MFusedSimpleOp (List.rev sops, f), ctx)

let make_exformula schema f =
  let init_ctx = { schema; pmap = Pred_map.empty; vmap = Var_map.empty } in
  let _, _ = translate_formula init_ctx f in
  "rofl"
