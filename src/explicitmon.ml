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
let explicit_mon_prefix = ref "."
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
module Pred_ty_map = Map.Make (Int)
module Var_map = New_id (Map.Make (String))
module String_set = Set.Make (String)

type var_id = int
type pred_id = int

let print_var_map vmap =
  Printf.eprintf "[%s]\n"
    (let slist =
       map
         (fun (name, id) -> Printf.sprintf "(%s -> %d)" name id)
         (List.of_seq (Var_map.to_seq vmap))
     in
     String.concat ", " slist)

let print_pmap pmap =
  Printf.eprintf "[%s]\n"
    (let slist =
       map
         (fun ((name, arity), id) ->
           Printf.sprintf "(%d -> (%s, %d))" id name arity)
         (List.of_seq (Pred_map.to_seq pmap))
     in
     String.concat ", " slist)

type translation_ctx = {
  fpmap : pred_id Pred_map.t;
  fptymap : (bool * tcst list) Pred_ty_map.t;
  vmap : var_id Var_map.t;
}

let print_vars ctx =
  let s =
    List.map
      (fun (var, id) -> Printf.sprintf "(%s, %d)" var id)
      (List.of_seq (Var_map.to_seq ctx.vmap))
  in
  Printf.printf "[%s]\n" (String.concat ", " s)

let filter_vars ctx keep_vars =
  let vmap = Var_map.filter (fun var _ -> List.mem var keep_vars) ctx.vmap in
  { ctx with vmap }

let maybe_add_var ctx name =
  let vmap, new_id = Var_map.maybe_make_new ctx.vmap name in
  ({ ctx with vmap }, new_id)

let overwrite_vars vmap1 vmap2 vars =
  let vmap1 =
    Var_map.merge
      (fun v id1 id2 -> if List.mem v vars then id2 else id1)
      vmap1 vmap2
  in
  vmap1

let maybe_add_pred ctx name arity builtin ptys =
  let fpmap, new_id = Pred_map.maybe_make_new ctx.fpmap (name, arity) in
  let fptymap = Pred_ty_map.add new_id (builtin, ptys) ctx.fptymap in
  ({ ctx with fpmap; fptymap }, new_id)

let overwrite_pred ctx name arity builtin ptys =
  let fpmap, old_id, new_id = Pred_map.make_new ctx.fpmap (name, arity) in
  let old_info =
    match old_id with
    | Some old_id -> Some (old_id, Pred_ty_map.find old_id ctx.fptymap)
    | None -> None
  in
  let fptymap = Pred_ty_map.add new_id (builtin, ptys) ctx.fptymap in
  ({ ctx with fpmap; fptymap }, new_id, old_info)

let overwrite_mult ctx preds =
  fold_left
    (fun (ctx, ps) (name, arity, builtin, ptys) ->
      let ctx, new_id, old_info = overwrite_pred ctx name arity builtin ptys in
      (ctx, (name, arity, new_id, old_info) :: ps))
    (ctx, []) preds

let restore_pred ctx name arity new_id old_info =
  let fpmap = Pred_map.remove (name, arity) ctx.fpmap in
  let fptymap = Pred_ty_map.remove new_id ctx.fptymap in
  let fpmap, fptymap =
    match old_info with
    | Some (old_id, old_tys) ->
        let fpmap = Pred_map.add (name, arity) old_id fpmap in
        let fptymap = Pred_ty_map.add old_id old_tys fptymap in
        (fpmap, fptymap)
    | None -> (fpmap, fptymap)
  in
  { ctx with fpmap; fptymap }

let restore_mult ctx infs =
  fold_left
    (fun ctx (name, arity, new_id, old_info) ->
      restore_pred ctx name arity new_id old_info)
    ctx infs

let ctx_of_sign sign =
  let fpmap = Pred_map.empty in
  let vmap = Var_map.empty in
  let all_d =
    filter_map
      (fun (name, tys) ->
        let arity = length tys in
        match (name, arity) with
        | "tp", 1 -> None
        | "ts", 1 -> None
        | "tpts", 2 -> None
        | _ -> Some ((name, arity), (false, map snd tys)))
      sign
  in
  let fpmap, _, ids = Pred_map.make_new_mult fpmap (map fst all_d) in
  let fptymap =
    map2 (fun a b -> (a, b)) ids (map snd all_d) |> to_seq |> Pred_ty_map.of_seq
  in
  { fpmap; vmap; fptymap }

let get_fv_types ctx f =
  let orig_fv = MFOTL.free_vars f in
  let s =
    Pred_map.fold
      (fun (name, arity) id ps ->
        let tys = snd (Pred_ty_map.find id ctx.fptymap) in
        let tys = map (fun t -> ("", t)) tys in
        (name, tys) :: ps)
      ctx.fpmap []
  in
  let fvtypes = fst (check_syntax s f) in
  List.map (fun v -> (v, List.assoc v fvtypes)) orig_fv

type cst_type = CstEq | CstLess | CstLessEq
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
  | MAndRel of bool * cst_type * term * term
  | MExists of var_id list

type predarg = PVar of tcst * var_id | PCst of cst
type bound = Bnd of tsdiff | Inf
type interval = bound * bound

type aggreg_info = {
  res_var : var_id;
  op : agg_op;
  agg_var : var_id;
  gvars : var_id list;
}

type exformula =
  | MPredicate of pred_id * predarg list
  | MLet of pred_id * var_id list * exformula * exformula
  | MLetPast of pred_id * var_id list * exformula * exformula
  | MTp of predarg
  | MTs of predarg
  | MTpts of predarg * predarg
  | MAnd of join_type * exformula * exformula
  | MOr of exformula * exformula
  | MNeg of exformula
  | MEq of term * term
  | MEmptyRel
  | MPrev of interval * exformula
  | MNext of interval * exformula
  | MOnce of interval * exformula
  | MOnceAgg of aggreg_info * interval * exformula
  | MSince of bool * interval * exformula * exformula
  | MSinceAgg of aggreg_info * bool * interval * exformula * exformula
  | MFusedSimpleOp of simple_op list * exformula
  | MUntil of bool * interval * exformula * exformula
  | MEventually of interval * exformula
  | MAggregation of aggreg_info * exformula

let translate_bnd upper = function
  | OBnd a ->
      if upper then Bnd (MFOTL.ts_minus a Z.one)
      else Bnd (MFOTL.ts_plus a Z.one)
  | CBnd a -> Bnd a
  | MFOTL.Inf -> Inf

let translate_intv (a, b) = (translate_bnd false a, translate_bnd true b)

let create_new_id =
  incr curr_id;
  !curr_id

let rec translate_term ctx t =
  let module P = Predicate in
  match t with
  | P.Var name ->
      let ctx, id = maybe_add_var ctx name in
      (TVar id, ctx)
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

let translate_pred_args ctx name arity terms =
  let module P = Predicate in
  let pred_id = Pred_map.find (name, arity) ctx.fpmap in
  let builtin, ptys = Pred_ty_map.find pred_id ctx.fptymap in
  let ctx, pargs, ptys =
    List.fold_left2
      (fun (ctx, trsfd, ptys) t ty ->
        match t with
        | P.Var name ->
            let ctx, new_id = maybe_add_var ctx name in
            let trsfd = PVar (ty, new_id) :: trsfd in
            (ctx, trsfd, ty :: ptys)
        | P.Cst (P.Int _ as cst) -> (ctx, PCst cst :: trsfd, TInt :: ptys)
        | P.Cst (P.Str _ as cst) -> (ctx, PCst cst :: trsfd, TStr :: ptys)
        | P.Cst (P.Float _ as cst) -> (ctx, PCst cst :: trsfd, TFloat :: ptys)
        | _ -> failwith "unsupported predicate arg")
      (ctx, [], []) terms ptys
  in
  (ctx, List.rev pargs, builtin, List.rev ptys)

let translate_pred ctx name arity terms =
  let ctx, trsfd, builtin, ptys = translate_pred_args ctx name arity terms in
  match (name, arity, builtin) with
  | "tp", 1, true -> (MTp (nth trsfd 0), ctx)
  | "ts", 1, true -> (MTs (nth trsfd 0), ctx)
  | "tpts", 2, true -> (MTpts (nth trsfd 0, nth trsfd 1), ctx)
  | _, _, true -> failwith "unknown builtin predicate"
  | _ ->
      let ctx, new_id = maybe_add_pred ctx name arity false ptys in
      (MPredicate (new_id, trsfd), ctx)

let is_special_and f1 f2 =
  let fv1 = MFOTL.free_vars f1 in
  is_and_relop f2 && is_special_case fv1 f2

let rec is_safe_assignment f1 f2 =
  let fv1 = String_set.of_list (MFOTL.free_vars f1) in
  match f2 with
  | Equal (Var a, Var b) -> String_set.mem a fv1 == not (String_set.mem b fv1)
  | Equal (Var a, t) ->
      (not (String_set.mem a fv1))
      && String_set.subset (String_set.of_list (Predicate.tvars t)) fv1
  | Equal (t, Var b) -> is_safe_assignment f1 (Equal (Var b, t))
  | _ -> false

let rec translate_formula ctx = function
  | Pred (name, arity, terms) -> translate_pred ctx name arity terms
  | Let ((name, arity, terms), f1, f2) ->
      let fvtys = get_fv_types ctx f1 in
      let pvars =
        map (function Var v -> v | _ -> failwith "not a var") terms
      in
      let ptys = map (fun v -> List.assoc v fvtys) pvars in
      let f1, ctx = translate_formula ctx f1 in
      let pvars = map (fun v -> Var_map.find v ctx.vmap) pvars in
      let ctx, new_id, old_info = overwrite_pred ctx name arity false ptys in
      let f2, ctx = translate_formula ctx f2 in
      let ctx = restore_pred ctx name arity new_id old_info in
      (MLet (new_id, pvars, f1, f2), ctx)
  | LetPast ((name, arity, terms), f1, f2) ->
      let ptys =
        match !letpast_types with
        | l :: ls ->
            letpast_types := ls;
            l
        | _ -> failwith "no typed found for letpast"
      in
      let pvars =
        map (function Var v -> v | _ -> failwith "not a var") terms
      in
      let ctx, new_id, old_info = overwrite_pred ctx name arity false ptys in
      let f1, ctx = translate_formula ctx f1 in
      let pvars = map (fun v -> Var_map.find v ctx.vmap) pvars in
      let f2, ctx = translate_formula ctx f2 in
      let ctx = restore_pred ctx name arity new_id old_info in
      (MLetPast (new_id, pvars, f1, f2), ctx)
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
      (MOnce (intv, f), ctx)
  | Eventually (intv, f) ->
      let f, ctx = translate_formula ctx f in
      let intv = translate_intv intv in
      (MEventually (intv, f), ctx)
  | Since (intv, Neg f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      let intv = translate_intv intv in
      (MSince (true, intv, f1, f2), ctx)
  | Since (intv, f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      let intv = translate_intv intv in
      (MSince (false, intv, f1, f2), ctx)
  | Until (intv, Neg f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      let intv = translate_intv intv in
      (MUntil (true, intv, f1, f2), ctx)
  | Until (intv, f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      let intv = translate_intv intv in
      (MUntil (false, intv, f1, f2), ctx)
  | Or (f1, f2) ->
      let ctx, f1, f2 = translate_two_seq ctx f1 f2 in
      (MOr (f1, f2), ctx)
  | Equal (t1, t2) ->
      let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
      (MEq (t1, t2), ctx)
  | Neg (Equal (Var a, Var b)) when a = b -> (MEmptyRel, ctx)
  | Neg f ->
      let f, ctx = translate_formula ctx f in
      (MNeg f, ctx)
  | Aggreg (_, res_var, op, agg_var, gvars, f) -> (
      let f, agg_ctx = translate_formula (filter_vars ctx gvars) f in
      let vmap = overwrite_vars ctx.vmap agg_ctx.vmap gvars in
      let ctx = { agg_ctx with vmap } in
      let ctx, res_var = maybe_add_var ctx res_var in
      let agg_var = Var_map.find agg_var agg_ctx.vmap in
      let gvars = map (fun var -> Var_map.find var agg_ctx.vmap) gvars in
      let info = { res_var; op; agg_var; gvars } in
      match f with
      | MOnce (intv, f) -> (MOnceAgg (info, intv, f), ctx)
      | MSince (b, intv, f1, f2) -> (MSinceAgg (info, b, intv, f1, f2), ctx)
      | _ -> (MAggregation (info, f), ctx))
  (* fused op cases *)
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
        let ctx, x = maybe_add_var ctx x in
        let ctx, y = maybe_add_var ctx y in
        let sop =
          if x_free then MAndAssign (y, TVar x)
          else if y_free then MAndAssign (x, TVar y)
          else failwith "should not happen"
        in
        (ctx, sop)
    | t, P.Var x | P.Var x, t ->
        let ctx, x = maybe_add_var ctx x in
        let t, ctx = translate_term ctx t in
        (ctx, MAndAssign (x, t))
    | _ -> failwith "lol"
  in
  transform_fused_op ctx (sop :: sops) f1

and translate_constraint ctx sops f1 f2 =
  let ctx, sop =
    match f2 with
    | Equal (t1, t2) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (false, CstEq, t1, t2))
    | LessEq (t1, t2) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (false, CstLessEq, t1, t2))
    | Less (t1, t2) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (false, CstLess, t1, t2))
    | Neg (Equal (t1, t2)) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (true, CstEq, t1, t2))
    | Neg (LessEq (t1, t2)) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (true, CstLessEq, t1, t2))
    | Neg (Less (t1, t2)) ->
        let ctx, t1, t2 = translate_two_terms ctx t1 t2 in
        (ctx, MAndRel (true, CstLess, t1, t2))
    | _ -> failwith "not a constraint"
  in
  transform_fused_op ctx (sop :: sops) f1

and transform_fused_op ctx sops = function
  | Exists (vars, f) ->
      let vmap, old_ids, new_ids = Var_map.make_new_mult ctx.vmap vars in
      let f, ctx =
        transform_fused_op { ctx with vmap } (MExists new_ids :: sops) f
      in
      let vmap = Var_map.update_all ctx.vmap vars old_ids in
      (f, { ctx with vmap })
  | And (f1, (Equal (x, y) as f2))
    when is_special_and f1 f2 && is_safe_assignment f1 f2 ->
      translate_safe_assignment ctx sops f1 (x, y)
  | And (f1, f2) when is_special_and f1 f2 ->
      translate_constraint ctx sops f1 f2
  | f ->
      let f, ctx = translate_formula ctx f in
      (MFusedSimpleOp (sops, f), ctx)

let join_ps_and_pty fpmap fptymap =
  Pred_map.fold
    (fun (name, arity) id preds ->
      let builtin, tys = Pred_ty_map.find id fptymap in
      assert (not builtin);
      (name, arity, id, tys) :: preds)
    fpmap []

let make_exformula sign f fvs =
  (* normalize the formula *)
  let f = Rewriting.elim_syntactic_sugar f in
  let ctx = ctx_of_sign sign in
  let ctx, infs =
    overwrite_mult ctx
      [
        ("tp", 1, true, [ TInt ]);
        ("ts", 1, true, [ TInt ]);
        ("tpts", 2, true, [ TInt; TInt ]);
      ]
  in
  let f, ctx = translate_formula ctx f in
  let ctx = restore_mult ctx infs in
  let fvs = map (fun v -> Var_map.find v ctx.vmap) fvs in
  let preds = join_ps_and_pty ctx.fpmap ctx.fptymap in
  (fvs, preds, f)

type cst_map = {
  scstmap : (string * string) list;
  fcstmap : (string * float) list;
}

let cst_id = ref 0

let get_new_cst_id =
  incr cst_id;
  !cst_id

(* here b is the print context *)
type 'b printable = Printable : ('a * ('b -> 'a -> 'b)) -> 'b printable

let print_printable cmap (Printable (p, pfn)) = pfn cmap p

let print_zint_cst cmap i =
  printf "mp_int64_t<%s>" (Z.to_string i);
  cmap

let print_bool cmap b =
  printf "%B" b;
  cmap

let print_int cmap i =
  printf "%d" i;
  cmap

let print_size_t_cst cmap i =
  printf "mp_size_t<%d>" i;
  cmap

let print_agg_op cmap op =
  (match op with
  | Max -> print_string "max_agg_op"
  | Min -> print_string "min_agg_op"
  | Avg -> print_string "avg_agg_op"
  | Sum -> print_string "sum_agg_op"
  | Cnt -> print_string "cnt_agg_op"
  | _ -> failwith "unsupported fragment");
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

let print_list cmap l pfn =
  let ps = map (fun e -> Printable (e, pfn)) l in
  print_printable_list cmap ps

let print_enclosed cmap sepo sepc body =
  print_string sepo;
  open_box 2;
  let cmap = body cmap in
  close_box ();
  print_string sepc;
  cmap

let print_template_body cmap pbody = print_enclosed cmap "<" ">" pbody

let print_template cmap name pbody =
  print_string name;
  print_template_body cmap pbody

let print_ty cmap ty =
  (match ty with
  | TInt -> print_string "std::int64_t"
  | TStr -> print_string "std::string"
  | TFloat -> print_string "double"
  | _ -> failwith "regex not supported");
  cmap

let print_arg_ty cmap ty =
  (match ty with
  | TInt -> print_string "INT_TYPE"
  | TStr -> print_string "STRING_TYPE"
  | TFloat -> print_string "FLOAT_TYPE"
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
            [ Printable (ty, print_ty); Printable (id, print_int) ])
  | PCst cst ->
      print_template cmap "pcst" (fun cmap ->
          print_printable_list cmap [ Printable (cst, print_cst) ])

let print_templ_ps_l cmap name ps =
  print_template cmap name (fun cmap -> print_printable_list cmap ps)

let print_templ_l cmap name l pfn =
  print_template cmap name (fun cmap -> print_list cmap l pfn)

let print_var_list cmap vars =
  if List.length vars == 0 then (
    print_string "mp_list<>";
    cmap)
  else
    print_templ_ps_l cmap "mp_list_c"
      (Printable
         ( (),
           fun cmap _ ->
             print_string "std::size_t";
             cmap )
      :: map (fun var -> Printable (var, print_int)) vars)

let print_jtype cmap = function
  | NatJoin -> print_bool cmap false
  | AntiJoin -> print_bool cmap true

let print_bound cmap = function
  | Bnd i -> print_size_t_cst cmap (Z.to_int i)
  | Inf ->
      print_string "inf_bound";
      cmap

let rec print_term cmap = function
  | TVar id -> print_template cmap "tvar" (fun cmap -> print_int cmap id)
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

let print_sop cmap = function
  | MAndAssign (res_var, t) ->
      print_templ_ps_l cmap "mandassign"
        [ Printable (res_var, print_int); Printable (t, print_term) ]
  | MAndRel (is_neg, ty, t1, t2) ->
      print_templ_ps_l cmap "mandrel"
        [
          Printable (is_neg, print_bool);
          Printable (ty, print_cst_ty);
          Printable (t1, print_term);
          Printable (t2, print_term);
        ]
  | MExists vars -> print_templ_l cmap "mexists" vars print_int

let print_sops cmap sops = print_templ_l cmap "simpleops" sops print_sop

let print_assignment cmap lhs_s rhs_p =
  print_string lhs_s;
  print_string " ";
  print_string "=";
  print_break 1 2;
  let cmap = print_printable cmap rhs_p in
  print_string ";";
  cmap

let aggreg_info_ps { res_var; op; agg_var; gvars } =
  [
    Printable (res_var, print_int);
    Printable (op, print_agg_op);
    Printable (agg_var, print_int);
    Printable (gvars, print_var_list);
  ]

let pred_args_ps args = map (fun arg -> Printable (arg, print_pred_arg)) args

let print_exformula f =
  let rec go cmap f =
    match f with
    | MPredicate (id, args) ->
        print_templ_ps_l cmap "mpredicate"
          (Printable (id, print_int) :: pred_args_ps args)
    | MLet (id, pvars, f1, f2) ->
        print_templ_ps_l cmap "mlet"
          [
            Printable (id, print_int);
            Printable (pvars, print_var_list);
            Printable (f1, go);
            Printable (f2, go);
          ]
    | MLetPast (id, pvars, f1, f2) ->
        print_templ_ps_l cmap "mletpast"
          [
            Printable (id, print_int);
            Printable (pvars, print_var_list);
            Printable (f1, go);
            Printable (f2, go);
          ]
    | MTp arg -> print_templ_ps_l cmap "mtp" [ Printable (arg, print_pred_arg) ]
    | MTs arg -> print_templ_ps_l cmap "mts" [ Printable (arg, print_pred_arg) ]
    | MTpts (arg1, arg2) ->
        print_templ_ps_l cmap "mtpts"
          [ Printable (arg1, print_pred_arg); Printable (arg2, print_pred_arg) ]
    | MAnd (jty, f1, f2) ->
        print_templ_ps_l cmap "mand"
          [
            Printable (jty, print_jtype); Printable (f1, go); Printable (f2, go);
          ]
    | MOr (f1, f2) ->
        print_templ_ps_l cmap "mor" [ Printable (f1, go); Printable (f2, go) ]
    | MNeg f -> print_templ_ps_l cmap "mneg" [ Printable (f, go) ]
    | MEq (t1, t2) ->
        print_templ_ps_l cmap "mequal"
          [ Printable (t1, print_term); Printable (t2, print_term) ]
    | MEmptyRel ->
        print_string "memptyrel";
        cmap
    | MPrev (intv, f) -> print_temp_op cmap "mprev" [] intv [ f ]
    | MNext (intv, f) -> print_temp_op cmap "mnext" [] intv [ f ]
    | MOnce (intv, f) -> print_temp_op cmap "monce" [] intv [ f ]
    | MOnceAgg (agginfo, intv, f) ->
        print_temp_op cmap "monceagg" (aggreg_info_ps agginfo) intv [ f ]
    | MSince (is_neg, intv, f1, f2) ->
        print_temp_op cmap "msince"
          [ Printable (is_neg, print_bool) ]
          intv [ f1; f2 ]
    | MSinceAgg (agginfo, is_neg, intv, f1, f2) ->
        print_temp_op cmap "msinceagg"
          (aggreg_info_ps agginfo @ [ Printable (is_neg, print_bool) ])
          intv [ f1; f2 ]
    | MUntil (is_neg, intv, f1, f2) ->
        print_temp_op cmap "muntil"
          [ Printable (is_neg, print_bool) ]
          intv [ f1; f2 ]
    | MEventually (intv, f) -> print_temp_op cmap "meventually" [] intv [ f ]
    | MAggregation ({ res_var; op; agg_var; gvars }, f) ->
        print_templ_ps_l cmap "maggregation"
          [
            Printable (res_var, print_int);
            Printable (op, print_agg_op);
            Printable (agg_var, print_int);
            Printable (gvars, print_var_list);
            Printable (f, go);
          ]
    | MFusedSimpleOp (sops, f) ->
        print_templ_ps_l cmap "mfusedsimpleop"
          [ Printable (sops, print_sops); Printable (f, go) ]
  and print_temp_op cmap name ps (lb, ub) rterms =
    let bnd_prints = map (fun b -> Printable (b, print_bound)) [ lb; ub ] in
    let rec_prints = map (fun r -> Printable (r, go)) rterms in
    print_templ_ps_l cmap name (concat [ ps; bnd_prints; rec_prints ])
  in
  let cmap =
    print_assignment
      { scstmap = []; fcstmap = [] }
      "using input_formula"
      (Printable (f, go))
  in
  print_newline ();
  cmap

let print_cst_struct sty sname scst =
  printf
    "struct %s {\nusing value_type = %s;\nstatic constexpr %s value = %s;\n};\n"
    sname sty sty scst

let print_cst_struct_list sty arg =
  let snames, scst = split arg in
  iter2 (print_cst_struct sty) snames scst

let print_exformula_csts cmap =
  print_cst_struct_list "std::string_view"
    (map (fun (a, b) -> (a, "\"" ^ b ^ "\"sv")) cmap.scstmap);
  print_cst_struct_list "double"
    (map (fun (a, b) -> (a, Float.to_string b)) cmap.fcstmap)

let print_fvs fvs =
  print_assignment () "using free_variables" (Printable (fvs, print_var_list));
  print_newline ()

let with_open_out_chan s f =
  let chan = open_out s in
  Fun.protect ~finally:(fun _ -> close_out chan) (fun _ -> f chan)

let print_braced_list ps =
  print_enclosed () "{" "}" (fun _ -> print_printable_list () ps)

let print_name_arity_tup (name, arity) =
  print_braced_list
    [
      Printable (name, fun _ name -> print_string name);
      Printable (arity, print_int);
    ]

let print_id_tys_pair (id, tys) =
  print_enclosed () "{" "}" (fun _ ->
      let ps = [ Printable (id, print_int) ] in
      print_printable_list () ps)

let print_pred cmap (name, _, id, tys) =
  print_braced_list
    [
      Printable (name, fun _ name -> print_string ("\"" ^ name ^ "\""));
      Printable
        ( (id, tys),
          fun _ (id, tys) ->
            print_braced_list
              [
                Printable (id, print_int);
                Printable
                  ( tys,
                    fun _ tys ->
                      print_braced_list
                        (List.map (fun ty -> Printable (ty, print_arg_ty)) tys)
                  );
              ] );
    ]

let print_preds preds =
  print_assignment () "inline static const pred_map_t input_predicates"
    (Printable
       ( preds,
         fun _ preds ->
           let ps = List.map (fun pred -> Printable (pred, print_pred)) preds in
           print_braced_list ps ));
  print_newline ()

let add_prefix_to fname = !explicit_mon_prefix ^ "/" ^ fname

let cpp_of_exformula f fvs preds =
  with_open_out_chan (add_prefix_to "formula_in.h") (fun chan ->
      set_formatter_out_channel chan;
      let cmap = print_exformula f in
      print_fvs fvs;
      print_preds preds;
      with_open_out_chan (add_prefix_to "formula_csts.h") (fun chan ->
          set_formatter_out_channel chan;
          print_exformula_csts cmap;
          print_newline ()))

let write_explicitmon_state sign f fvs =
  let fvs, preds, f = make_exformula sign f fvs in
  cpp_of_exformula f fvs preds
