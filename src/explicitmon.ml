open MFOTL
open Rewriting
open Predicate
open Table
open String
open Map
open Set
open List
open Db
open Format

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

type cst_type = CstEq | CstLess | CstLessEq
type cst_neg = Negated | Normal
type join_type = NatJoin | AntiJoin

type term =
  | TVar of var_id
  | TCst of cst
  | F2i of term
  | I2f of term
  | Plus of term * term
  | Minus of term * term
  | UMinus of term
  | Mult of term * term
  | Div of term * term
  | Mod of term * term

type simple_op =
  | MAndAssign of var_id * term
  | MAndRel of cst_neg * cst_type * term * term
  | MExists of var_id list

type predarg = PVar of tcst * var_id | PCst of cst
type bound = Bnd of tsdiff | Inf
type interval = bound * bound

type exformula =
  | MPredicate of pred_id * predarg list
  | MTp of predarg
  | MTs of predarg
  | MTpts of predarg * predarg
  | MAnd of join_type * exformula * exformula
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

let create_new_id =
  incr curr_id;
  !curr_id

let rec translate_term ctx t =
  let module P = Predicate in
  match t with
  | P.Var name ->
      let vmap, id = Var_map.maybe_make_new ctx.vmap name in
      (TVar id, { ctx with vmap })
  | P.Cst cst -> (TCst cst, ctx)
  | P.F2i t -> translate_term ctx t
  | P.I2f t -> translate_term ctx t
  | P.Plus (t1, t2) ->
      let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
      (Plus (t1, t2), ctx)
  | P.Minus (t1, t2) ->
      let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
      (Minus (t1, t2), ctx)
  | P.Mult (t1, t2) ->
      let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
      (Mult (t1, t2), ctx)
  | P.Div (t1, t2) ->
      let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
      (Mod (t1, t2), ctx)
  | _ -> failwith "unsupported term"

and translate_two_terms ctx t1 t2 =
  let t1, ctx = translate_term ctx t1 in
  let t2, ctx = translate_term ctx t2 in
  (ctx, t1, t2)

let translate_pred_args schema_entry vmap terms =
  let module P = Predicate in
  let vmap, ret, _ =
    List.fold_left
      (fun (vmap, trsfd, idx) t ->
        match t with
        | P.Var name ->
            let vmap, new_id = Var_map.maybe_make_new vmap name in
            let ty = snd (nth schema_entry idx) in
            let trsfd = PVar (ty, new_id) :: trsfd in
            (vmap, trsfd, idx + 1)
        | P.Cst cst -> (vmap, PCst cst :: trsfd, idx + 1)
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

let is_special_and f1 f2 =
  let fv1 = MFOTL.free_vars f1 in
  is_and_relop f2 && is_special_case fv1 f2

let rec is_safe_assignment f1 f2 =
  let fv2 = String_set.of_list (MFOTL.free_vars f2) in
  match f2 with
  | Equal (Var a, Var b) -> String_set.mem a fv2 == String_set.mem b fv2
  | Equal (Var a, t) ->
      (not (String_set.mem a fv2))
      && String_set.subset (String_set.of_list (Predicate.tvars t)) fv2
  | Equal (t, Var b) -> is_safe_assignment f1 (Equal (Var b, t))
  | _ -> false

let rec translate_formula ctx = function
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
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      let intv = translate_intv intv in
      let f =
        match if_unbounded intv with
        | Some k -> MSinceU (k, f1, f2)
        | None -> MSinceB (intv, f1, f2)
      in
      (f, ctx)
  | Until (intv, f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      (MUntil (translate_intv intv, f1, f2), ctx)
  | Or (f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      (MOr (f1, f2), ctx)
  | Exists (_, _) as f -> transform_fused_op ctx [] f
  | And (f1, f2) as f when is_special_and f1 f2 ->
      (* possibly a fused op *)
      transform_fused_op ctx [] f
  | And (f1, Neg f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      (MAnd (AntiJoin, f1, f2), ctx)
  | And (f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      (MAnd (NatJoin, f1, f2), ctx)
  | PastAlways _ | Always _ | Implies _ | Equiv _ | ForAll _ ->
      failwith "should have been eliminated by desugaring"
  | _ -> failwith "unsupported fragment"

and translate_two_seq ctx f1 f2 =
  let f1, ctx = translate_formula ctx f1 in
  let f2, ctx = translate_formula ctx f2 in
  (ctx, f1, f2)

and translate_safe_assignment ctx sops f1 (x, y) =
  let module P = Predicate in
  let ctx, sop =
    match (x, y) with
    | P.Var x, P.Var y ->
        let fv1 = String_set.of_list (MFOTL.free_vars f1) in
        let x_free = String_set.mem x fv1 in
        let y_free = String_set.mem y fv1 in
        let vmap, x = Var_map.maybe_make_new ctx.vmap x in
        let vmap, y = Var_map.maybe_make_new vmap y in
        let ctx = { ctx with vmap } in
        let sop =
          if x_free then MAndAssign (y, TVar x)
          else if y_free then MAndAssign (x, TVar y)
          else failwith "should not happen"
        in
        (ctx, sop)
    | t, P.Var x | P.Var x, t ->
        let vmap, x = Var_map.maybe_make_new ctx.vmap x in
        let t, ctx = translate_term { ctx with vmap } t in
        (ctx, MAndAssign (x, t))
    | _ -> failwith "lol"
  in
  transform_fused_op ctx (sop :: sops) f1

and translate_constraint ctx sops f1 f2 =
  let ctx, sop =
    match f2 with
    | Equal (t1, t2) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (Normal, CstEq, t1, t2))
    | LessEq (t1, t2) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (Normal, CstLessEq, t1, t2))
    | Less (t1, t2) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (Normal, CstLess, t1, t2))
    | Neg (Equal (t1, t2)) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (Negated, CstEq, t1, t2))
    | Neg (LessEq (t1, t2)) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (Normal, CstLessEq, t1, t2))
    | Neg (Less (t1, t2)) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (Negated, CstLess, t1, t2))
    | _ -> failwith "not a constraint"
  in
  transform_fused_op ctx (sop :: sops) f1

and transform_fused_op ctx sops = function
  | Exists (vars, f) ->
      let vmap, old_ids, new_ids = Var_map.make_new_mult ctx.vmap vars in
      let f, ctx =
        transform_fused_op { ctx with vmap } (MExists new_ids :: sops) f
      in
      let vmap = Var_map.update_all vmap vars old_ids in
      (f, { ctx with vmap })
  | And (f1, (Equal (x, y) as f2))
    when is_special_and f1 f2 && is_safe_assignment f1 f2 ->
      translate_safe_assignment ctx sops f1 (x, y)
  | And (f1, f2) when is_special_and f1 f2 ->
      translate_constraint ctx sops f1 f2
  | f ->
      let f, ctx = translate_formula ctx f in
      (MFusedSimpleOp (List.rev sops, f), ctx)

let make_exformula schema f =
  (* normalize the formula *)
  let f = Rewriting.elim_syntactic_sugar f in
  let init_ctx = { schema; pmap = Pred_map.empty; vmap = Var_map.empty } in
  fst (translate_formula init_ctx f)

type cst_map = {
  scstmap : (string * string) list;
  fcstmap : (string * float) list;
}

let cst_id = ref 0

let get_new_cst_id =
  incr cst_id;
  !cst_id

type printable = Printable : ('a * (cst_map -> 'a -> cst_map)) -> printable

let print_printable cmap (Printable (p, pfn)) = pfn cmap p

let print_zint_cst cmap i =
  printf "mp_long<%s>" (Z.to_string i);
  cmap

let print_int_cst cmap i =
  printf "mp_long<%d>" i;
  cmap

let print_string_cst cmap s =
  let var_name = "string_cst_" ^ string_of_int get_new_cst_id in
  print_string var_name;
  { cmap with scstmap = (var_name, s) :: cmap.scstmap }

let print_float_cst cmap f =
  let var_name = "float_cst_" ^ string_of_int get_new_cst_id in
  print_string var_name;
  { cmap with fcstmap = (var_name, f) :: cmap.fcstmap }

let rec print_printable_list cmap ps =
  match ps with
  | p1 :: p2 :: ps ->
      let cmap = print_printable cmap p1 in
      print_string ",";
      print_space ();
      print_printable_list cmap (p2 :: ps)
  | [ p ] -> print_printable cmap p
  | [] -> cmap

let rec print_list cmap l pfn =
  let ps = map (fun e -> Printable (e, pfn)) l in
  print_printable_list cmap ps

let print_template_body cmap pbody =
  print_string "<";
  open_box 1;
  let cmap = pbody cmap in
  close_box ();
  print_string ">";
  cmap

let print_template cmap name pbody =
  print_string name;
  print_template_body cmap pbody

let print_ty cmap ty =
  (match ty with
  | TInt -> print_string "int64_t"
  | TStr -> print_string "std::string"
  | TFloat -> print_string "double"
  | _ -> failwith "regex not supported");
  cmap

let print_cst cmap = function
  | Int i -> print_zint_cst cmap i
  | Str s -> print_string_cst cmap s
  | Float f -> print_float_cst cmap f
  | Regexp _ -> failwith "regex not supported"

let rec print_pred_arg cmap arg =
  match arg with
  | PVar (ty, id) ->
      print_template cmap "pvar" (fun cmap ->
          print_printable_list cmap
            [ Printable (ty, print_ty); Printable (id, print_int_cst) ])
  | PCst cst ->
      print_template cmap "pcst" (fun cmap ->
          print_printable_list cmap [ Printable (cst, print_cst) ])

let print_pred_args cmap args =
  print_template cmap "pred_args" (fun cmap ->
      print_list cmap args print_pred_arg)

let print_templ_ps_l cmap name ps =
  print_template cmap name (fun cmap -> print_printable_list cmap ps)

let print_templ_l cmap name l pfn =
  print_template cmap name (fun cmap -> print_list cmap l pfn)

let print_bool cmap b =
  Format.print_bool b;
  cmap

let print_jtype cmap = function
  | NatJoin -> print_bool cmap true
  | AntiJoin -> print_bool cmap false

let print_bound cmap = function
  | Bnd i -> print_zint_cst cmap i
  | Inf ->
      print_string "inf_bound";
      cmap

let rec print_term cmap = function
  | TVar id -> print_template cmap "tvar" (fun cmap -> print_int_cst cmap id)
  | TCst cst -> print_template cmap "tcst" (fun cmap -> print_cst cmap cst)
  | F2i t -> print_rec_term cmap "tf2i" [ t ]
  | I2f t -> print_rec_term cmap "ti2f" [ t ]
  | Plus (t1, t2) -> print_rec_term cmap "tplus" [ t1; t2 ]
  | Minus (t1, t2) -> print_rec_term cmap "tminus" [ t1; t2 ]
  | UMinus t -> print_rec_term cmap "tuminus" [ t ]
  | Mult (t1, t2) -> print_rec_term cmap "tmult" [ t1; t2 ]
  | Div (t1, t2) -> print_rec_term cmap "tplus" [ t1; t2 ]
  | Mod (t1, t2) -> print_rec_term cmap "tmod" [ t1; t2 ]

and print_rec_term cmap name ts = print_templ_l cmap name ts print_term

let print_cst_ty cmap ty =
  (match ty with
  | CstEq -> print_string "cst_eq"
  | CstLess -> print_string "cst_less"
  | CstLessEq -> print_string "cst_less_eq");
  cmap

let print_cst_neg cmap = function
  | Negated -> print_bool cmap true
  | Normal -> print_bool cmap false

let print_sop cmap = function
  | MAndAssign (res_var, t) ->
      print_templ_ps_l cmap "mandassign"
        [ Printable (res_var, print_int_cst); Printable (t, print_term) ]
  | MAndRel (is_neg, ty, t1, t2) ->
      print_templ_ps_l cmap "mandrel"
        [
          Printable (is_neg, print_cst_neg);
          Printable (ty, print_cst_ty);
          Printable (t1, print_term);
          Printable (t2, print_term);
        ]
  | MExists vars -> print_templ_l cmap "mexists" vars print_int_cst

let print_sops cmap sops = print_templ_l cmap "simpleops" sops print_sop

let rec print_exformula cmap = function
  | MPredicate (id, args) ->
      print_templ_ps_l cmap "mpredicate"
        [ Printable (id, print_int_cst); Printable (args, print_pred_args) ]
  | MTp arg -> print_templ_ps_l cmap "mtp" [ Printable (arg, print_pred_arg) ]
  | MTs arg -> print_templ_ps_l cmap "mts" [ Printable (arg, print_pred_arg) ]
  | MTpts (arg1, arg2) ->
      print_templ_ps_l cmap "mtpts"
        [ Printable (arg1, print_pred_arg); Printable (arg2, print_pred_arg) ]
  | MAnd (jty, f1, f2) ->
      print_templ_ps_l cmap "mand"
        [
          Printable (jty, print_jtype);
          Printable (f1, print_exformula);
          Printable (f2, print_exformula);
        ]
  | MOr (f1, f2) ->
      print_templ_ps_l cmap "mor"
        [ Printable (f1, print_exformula); Printable (f2, print_exformula) ]
  | MNeg f -> print_templ_ps_l cmap "mneg" [ Printable (f, print_exformula) ]
  | MPrev ((lb, ub), f) -> print_temp_op cmap "mprev" [ lb; ub ] [ f ]
  | MNext ((lb, ub), f) -> print_temp_op cmap "mnext" [ lb; ub ] [ f ]
  | MOnceB ((lb, ub), f) -> print_temp_op cmap "monceb" [ lb; ub ] [ f ]
  | MOnceU (b, f) -> print_temp_op cmap "monceu" [ Bnd b ] [ f ]
  | MSinceB ((lb, ub), f1, f2) ->
      print_temp_op cmap "msinceb" [ lb; ub ] [ f1; f2 ]
  | MSinceU (b, f1, f2) -> print_temp_op cmap "msinceu" [ Bnd b ] [ f1; f2 ]
  | MUntil ((lb, ub), f1, f2) ->
      print_temp_op cmap "muntil" [ lb; ub ] [ f1; f2 ]
  | MEventually ((lb, ub), f) ->
      print_temp_op cmap "meventually" [ lb; ub ] [ f ]
  | MFusedSimpleOp (sops, f) ->
      print_templ_ps_l cmap "mfusedsimpleop"
        [ Printable (sops, print_sops); Printable (f, print_exformula) ]

and print_temp_op cmap name bnds rterms =
  let bnd_prints = map (fun b -> Printable (b, print_bound)) bnds in
  let rec_prints = map (fun r -> Printable (r, print_exformula)) rterms in
  print_templ_ps_l cmap name (concat [ bnd_prints; rec_prints ])

let print_cst_struct sty sname scst =
  printf "struct %s {\nstatic constexpr %s = %s;\n};\n" sname sty scst

let print_cst_struct_list sty arg =
  let snames, scst = split arg in
  iter2 (print_cst_struct sty) snames scst

let print_exformula_csts cmap =
  print_cst_struct_list "std::string"
    (map (fun (a, b) -> (a, "\"" ^ b ^ "\"")) cmap.scstmap);
  print_cst_struct_list "double"
    (map (fun (a, b) -> (a, Float.to_string b)) cmap.fcstmap)

let cpp_of_exformula f = 
  let cmap = print_exformula {scstmap = []; fcstmap = []} f in
  print_newline ();
  print_exformula_csts cmap

let write_explicitmon_state (schema: Db.schema) (f: MFOTL.formula) =
  let f = make_exformula schema f in
  cpp_of_exformula f
