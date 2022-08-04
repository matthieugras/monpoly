open Relation
open Predicate
open MFOTL
open Tuple

module Sk = Dllist
module Sj = Dllist

type info  = (int * timestamp * relation) Queue.t
type linfo = {mutable llast: Neval.cell}
type ainfo = {mutable arel: relation option}
type pinfo = {mutable plast: Neval.cell}
type ninfo = {mutable init: bool}
type oainfo = {mutable ores: relation;
         oaauxrels: (timestamp * relation) Mqueue.t}

type agg_info = {op: agg_op; default: cst}

type ozinfo = {mutable oztree: (int, relation) Sliding.stree;
               mutable ozlast: (int * timestamp * relation) Dllist.cell;
               ozauxrels: (int * timestamp * relation) Dllist.dllist}
type oinfo = {mutable otree: (timestamp, relation) Sliding.stree;
              mutable olast: (timestamp * relation) Dllist.cell;
              oauxrels: (timestamp * relation) Dllist.dllist}
type sinfo = {mutable srel2: relation option;
              saux: Optimized_mtl.msaux}
type ezinfo = {mutable ezlastev: Neval.cell;
               mutable eztree: (int, relation) Sliding.stree;
               mutable ezlast: (int * timestamp * relation) Dllist.cell;
               ezauxrels: (int * timestamp * relation) Dllist.dllist}
type einfo = {mutable elastev: Neval.cell;
              mutable etree: (timestamp, relation) Sliding.stree;
              mutable elast: (timestamp * relation) Dllist.cell;
              eauxrels: (timestamp * relation) Dllist.dllist}
type uinfo = {mutable ulast: Neval.cell;
              mutable ufirst: bool;
              mutable ures: relation;
              mutable urel2: relation option;
              raux: (int * timestamp * (int * relation) Sk.dllist) Sj.dllist;
              mutable saux: (int * relation) Sk.dllist}
type uninfo = {mutable last1: Neval.cell;
               mutable last2: Neval.cell;
               mutable listrel1: (int * timestamp * relation) Dllist.dllist;
               mutable listrel2: (int * timestamp * relation) Dllist.dllist}

type comp_one = relation -> relation
type comp_two = relation -> relation -> relation

type extformula =
  | ERel of relation * int
  | EPred of predicate * comp_one * info * int
  | ELet of predicate * comp_one * extformula * extformula * linfo * int
  | ENeg of extformula * int
  | EAnd of comp_two * extformula * extformula * ainfo * int
  | EOr of comp_two * extformula * extformula * ainfo * int
  | EExists of comp_one * extformula * int
  | EAggreg of agg_info * Aggreg.aggregator * extformula * int
  | EAggOnce of agg_info * Aggreg.once_aggregator * extformula * int
  | EPrev of interval * extformula * pinfo * int
  | ENext of interval * extformula * ninfo * int
  | ESince of extformula * extformula * sinfo * int
  | EOnceA of interval * extformula * oainfo * int
  | EOnceZ of interval * extformula * ozinfo * int
  | EOnce of interval * extformula * oinfo * int
  | ENUntil of comp_two * interval * extformula * extformula * uninfo * int
  | EUntil of comp_two * interval * extformula * extformula * uinfo * int
  | EEventuallyZ of interval * extformula * ezinfo * int
  | EEventually of interval * extformula * einfo * int

val contains_eventually: extformula -> bool

val prerr_auxel:  int * Relation.relation -> unit
val prerr_sauxel: MFOTL.timestamp * Relation.relation -> unit

val prerr_predinf: string -> info -> unit
val prerr_uinf: string -> uinfo -> unit

val prerr_einfn: string -> einfo -> unit
val prerr_ezinf: string -> ezinfo -> unit

val prerr_extf: string -> extformula -> unit

val extf_structure: extformula -> string
