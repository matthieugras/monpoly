open Extformula
open Predicate
open Relation
open Tuple
open MFOTL

(* Immutable version of types used in eformula *)
type mozinfo = { mozauxrels: (int * timestamp * relation) Dllist.dllist}

type moinfo  = { moauxrels: (timestamp * relation) Dllist.dllist}

type msinfo  = { msrel2: relation option;
                 msaux: Optimized_mtl.msaux}

type mezinfo = { mezlastev: Neval.cell;
                 mezauxrels: (int * timestamp * relation) Dllist.dllist}

type meinfo  = { melastev: Neval.cell;
                 meauxrels: (timestamp * relation) Dllist.dllist}


(*  IMPORTANT/TODO
    The int pointers in the marshalled states can only be used if we work under the assumption that:
    1. Each split state marshals the whole formula (given by implementation)
    2. Each Monpoly instance receives all timepoints, without filtering at the source (dependent on the scope of the project)

    If 2. is no longer given by the project, the pointers will be different for different Monpoly instances and can no longer just be combined when merging
*)
type muinfo  = { mulast   :  Neval.cell;
                 mufirst  :  bool;
                 mures    :  relation;
                 murel2   :  relation option;
                 mraux    :  (int * timestamp * (int * relation) Sk.dllist) Sj.dllist;
                 msaux    :  (int * relation) Sk.dllist}
type muninfo = { mlast1   :  Neval.cell;
                 mlast2   :  Neval.cell;
                 mlistrel1:  (int * timestamp * relation) Dllist.dllist;
                 mlistrel2:  (int * timestamp * relation) Dllist.dllist;}

(* Immutable version of eformula used for marshalling *)
type mformula =
  | MRel of relation * int
  | MPred of predicate * comp_one * info * int
  | MLet of predicate * comp_one * mformula * mformula * Neval.cell * int
  | MNeg of mformula * int
  | MAnd of comp_two * mformula * mformula * ainfo * int
  | MOr of comp_two * mformula * mformula * ainfo * int
  | MExists of comp_one * mformula * int
  | MAggreg of agg_info * Aggreg.aggregator * mformula * int
  | MAggOnce of agg_info * Aggreg.once_aggregator * mformula * int
  | MPrev of interval * mformula * pinfo * int
  | MNext of interval * mformula * ninfo * int
  | MSince of mformula * mformula * sinfo * int
  | MOnceA of interval * mformula * oainfo * int
  | MOnceZ of interval * mformula * mozinfo * int
  | MOnce of interval * mformula  * moinfo * int
  | MNUntil of comp_two * interval * mformula * mformula * muninfo * int
  | MUntil of comp_two * interval * mformula * mformula * muinfo * int
  | MEventuallyZ of interval * mformula * mezinfo * int
  | MEventually of interval * mformula * meinfo * int

(* For each formula, returns list of relevant free variables according to sub structure *)
let free_vars f =
  let pvars p = Predicate.pvars p in
  let rec get_pred = function
  | MRel           (_, _)                    -> []
  | MPred          (p, c, _, _)              -> (pvars p)
  | MLet           (_, _, f1, f2, _, _)      -> get_pred f2
  | MNeg           (f1, _)                   -> get_pred f1
  | MAnd           (c, f1, f2, _, _)         -> Misc.union (get_pred f1) (get_pred f2)
  | MOr            (c, f1, f2, _, _)         -> Misc.union (get_pred f1) (get_pred f2)
  (* Utilize comp to map away unwanted elements of pvars *)
  | MExists        (c, f1, _)                -> Helper.rel_to_pvars (c (Helper.pvars_to_rel (get_pred f1)))
  | MAggreg        (_inf, _comp, f1, _)      -> get_pred f1
  | MAggOnce       (_inf, _state, f1, _)     -> get_pred f1
  | MPrev          (_, f1, _, _)             -> get_pred f1
  | MNext          (_, f1, _, _)             -> get_pred f1
  | MSince         (f1, f2, _, _)            -> Misc.union (get_pred f1) (get_pred f2)
  | MOnceA         (_, f1, _, _)             -> get_pred f1
  | MOnceZ         (_, f1, _, _)             -> get_pred f1
  | MOnce          (_, f1, _, _)             -> get_pred f1
  | MNUntil        (c, _, f1, f2, _, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MUntil         (c, _, f1, f2, _, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MEventuallyZ   (_, f1, _, _)             -> get_pred f1
  | MEventually    (_, f1, _, _)             -> get_pred f1
  in
  get_pred f

  (* For each formula, returns list of relevant free variables according to sub structure *)
let predicates f =
  let rec get_pred = function
  | MRel           (_, _)                    -> []
  | MPred          (p, _, _, _)              -> p :: []
  | MLet           (p, _, f1, f2, _, _)      -> Misc.union (get_pred f1)
      (List.filter (fun q -> Predicate.get_name p <> Predicate.get_name q) (get_pred f2))
  | MNeg           (f1, _)                   -> get_pred f1
  | MAnd           (_, f1, f2, _, _)         -> Misc.union (get_pred f1) (get_pred f2)
  | MOr            (_, f1, f2, _, _)         -> Misc.union (get_pred f1) (get_pred f2)
  (* Utilize comp to map away unwanted elements of pvars *)
  | MExists        (comp, f1, _)             -> get_pred f1
  | MAggreg        (_inf, _comp, f1, _)      -> get_pred f1
  | MAggOnce       (_inf, _state, f1, _)     -> get_pred f1
  | MPrev          (_, f1, _, _)             -> get_pred f1
  | MNext          (_, f1, _, _)             -> get_pred f1
  | MSince         (f1, f2, _, _)            -> Misc.union (get_pred f1) (get_pred f2)
  | MOnceA         (_, f1, _, _)             -> get_pred f1
  | MOnceZ         (_, f1, _, _)             -> get_pred f1
  | MOnce          (_, f1, _, _)             -> get_pred f1
  | MNUntil        (_, _, f1, f2, _, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MUntil         (_, _, f1, f2, _, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MEventuallyZ   (_, f1, _, _)             -> get_pred f1
  | MEventually    (_, f1, _, _)             -> get_pred f1
  in
  get_pred f
