(*<*)
theory Monitor_Code
  imports Monitor
  "HOL-Library.Code_Target_Nat"
  "HOL.String"
  Containers.Containers
  SWA
begin
(*>*)



lemma [code_unfold del, symmetric, code_post del]: "card \<equiv> Cardinality.card'" by simp
declare [[code drop: card]] Set_Impl.card_code[code]

instantiation enat :: ceq begin
definition ceq_enat where "ceq_enat = Some ((=) :: enat \<Rightarrow> _)"

instance by intro_classes (simp add: ceq_enat_def)
end

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then Eq else if x < y then Lt else Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance by intro_classes
end

derive ccompare Formula.trm
derive (eq) ceq Formula.trm
derive (rbt) set_impl Formula.trm
derive (eq) ceq Monitor.mregex
derive ccompare Monitor.mregex
derive (rbt) set_impl Monitor.mregex
derive (rbt) mapping_impl Monitor.mregex
derive (no) cenum Monitor.mregex

type_synonym 'a msaux = "nat \<times> \<I> \<times> (ts \<times> 'a table) list"

global_interpretation default: msaux
  "\<lambda>w (nt, I, xs) ys. I = ivl w \<and> current w = nt \<and> xs = ys"
  "\<lambda>I. (0, I, [] :: (ts \<times> 'a table) list)"
  "\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs)"
  "\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs)"
  "\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs)"
  "\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {}"
  defines minit0 = "msaux.minit0 (\<lambda>I. (0, I, [] :: (ts \<times> 'a table) list)) :: nat \<Rightarrow> 'a Formula.formula \<Rightarrow> ( 'a msaux, 'a) mformula"
  and minit = "msaux.minit (\<lambda>I. (0, I, [] :: (ts \<times> 'a table) list)):: 'a Formula.formula \<Rightarrow> ( 'a msaux, 'a) mstate"
  and minit_safe = "msaux.minit_safe (\<lambda>I. (0, I, [] :: (ts \<times> 'a table) list)) :: 'a Formula.formula \<Rightarrow> ( 'a msaux, 'a) mstate"
  and update_since = "msaux.update_since
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and meval = "msaux.meval
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and mstep = "msaux.mstep
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and msteps0_stateless = "msaux.msteps0_stateless
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and msteps_stateless = "msaux.msteps_stateless
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and monitor = "msaux.monitor (\<lambda>I. (0, I, []))
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  by unfold_locales (auto simp: init_window_def split: list.splits)
(*
(*
definition update_since :: "\<I> \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow>
  'a msaux \<Rightarrow> 'a table \<times> 'a msaux" where
  "update_since I pos rel1 rel2 nt aux =
    (let auxrest0 = [(t, join rel pos rel1). (t, rel) \<leftarrow> snd aux];
         auxrest0' = (case auxrest0 of
             [] \<Rightarrow> (nt, rel2) # map (\<lambda>i. (i, empty_table)) (rev [r (fst aux) ..< nt])
           | x # aux' \<Rightarrow> (if fst x = nt then (fst x, snd x \<union> rel2) # aux'
              else (nt, rel2) # map (\<lambda>i. (i, empty_table)) (rev [Suc (fst x) ..< nt]) @ (x # aux')));
         auxtree0 = map_tree (\<lambda>rel. join rel pos rel1) (fst aux);
         auxtree' =
           (if r auxtree0 = Suc nt then
              update_rightmost (\<lambda>rel. rel + rel2) auxtree0
            else if Suc nt - left I > 0 then
              (let window = (max 1 (the_enat (enat (Suc nt) - right I)), Suc nt - left I);
                   new_atoms = drop (left I) auxrest0'
               in slide' (rev (map snd new_atoms)) auxtree0 window)
            else auxtree0)
     in (if Suc nt - left I > 0 then the (val auxtree') else empty_table, (auxtree', take (left I) auxrest0')))"
*)

(*
  "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux ne \<longleftrightarrow>
    (\<exists>auxlist.
      l (fst aux) = (if ne = 0 then 0 else if Suc (\<tau> \<sigma> (ne-1)) - left I > 0 then max 1 (the_enat (enat (Suc (\<tau> \<sigma> (ne-1))) - right I)) else 0) \<and>
      r (fst aux) = (if ne = 0 then 0 else Suc (\<tau> \<sigma> (ne-1)) - left I) \<and>
      take (left I) auxlist = snd aux \<and>
      valid (replicate (l (fst aux) - 1) empty_table @ rev (map snd (drop (left I) auxlist))) (fst aux) \<and>
      sorted_wrt (\<lambda>x y. fst x > fst y) auxlist \<and>
      (\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and>
        (if (\<exists>i. \<tau> \<sigma> i = t) then qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>)) X else X = empty_table)) \<and>
      (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<longrightarrow>
        (\<exists>X. (t, X) \<in> set auxlist)))"
*)
fun fill where
  "fill ((t, X) # (u, Y) # xs) = (t, X) # map (\<lambda>t. (t, empty_table)) [t + 1 ..< u] @ fill ((u, Y) # xs)"
| "fill xs = xs"

lemma join_empty_table[simp]: "join empty_table pos rel = empty_table"
  by (auto simp: Table.join_def empty_table_def)

lemma map_join_fill:
  "map (\<lambda>(t, X). (t, join X pos rel)) (fill xs) = fill (map (\<lambda>(t, X). (t, join X pos rel)) xs)"
  by (induct xs rule: fill.induct) (auto simp: drop_Cons' gr0_conv_Suc drop_map)

lemma map_join_take_fill:
  "map (\<lambda>(t, X). (t, join X pos rel)) (take n (fill xs)) = take n (fill (map (\<lambda>(t, X). (t, join X pos rel)) xs))"
  by (auto simp: take_map[symmetric] map_join_fill)

lemma map_join_drop_fill:
  "map (\<lambda>(t, X). (t, join X pos rel)) (drop n (fill xs)) = drop n (fill (map (\<lambda>(t, X). (t, join X pos rel)) xs))"
  by (auto simp: drop_map[symmetric] map_join_fill)

lemma join_distr: "join (A \<union> B) pos C = join A pos C \<union> join B pos C"
  by (cases pos) (auto simp: join_False_code join_True_code)

lemma map_snd_flip: "map f (map snd xs) = map snd (map (\<lambda>(a, b). (a, f b)) xs)"
  by (auto simp: list.map_comp fun_eq_iff)

global_interpretation swa: msaux
  "\<lambda>w (I, t, xs) ys.
     let auxlist = fill ys in
     ivl w = I \<and>
     current w = r t + length xs - Suc 0 \<and>
     take (left (ivl w)) auxlist = xs \<and>
     valid (replicate (l t - 1) empty_table @ rev (map snd (drop (left (ivl w)) auxlist))) t \<and>
     l t = (if t = Leaf then 0 else earliest w + Suc 0) \<and>
     r t = (if t = Leaf then 0 else latest w + Suc 0)"
  "\<lambda>I. (I, Leaf, [])"
  "undefined"
  "\<lambda>pos rel (I, t, xs). (I, map_tree (\<lambda>X. join X pos rel) t, map (\<lambda>(t, X). (t, join X pos rel)) xs)"
  "\<lambda>(nt, X) (I, t, xs).
    let xs' =
      (case xs of [] \<Rightarrow> (nt, X) # map (\<lambda>i. (i, empty_table)) (rev [r t ..< nt])
           | x # aux' \<Rightarrow> (if fst x = nt then (fst x, snd x \<union> X) # aux'
              else (nt, X) # map (\<lambda>i. (i, empty_table)) (rev [Suc (fst x) ..< nt])));
      t' = (if r t = Suc nt then
              update_rightmost (\<lambda>rel. rel + X) t
            else if Suc nt - left I > 0 then
              (let window = (max 1 (the_enat (enat (Suc nt) - right I)), Suc nt - left I);
                   new_atoms = drop (left I) xs'
               in slide' (rev (map snd new_atoms)) t window)
            else t)
    in (I, t', xs')"
  "\<lambda>(I, t, xs). case val t of None \<Rightarrow> empty_table | Some X \<Rightarrow> X"
  apply unfold_locales
  subgoal by (auto simp: valid_Leaf init_window_def)
  subgoal sorry
  subgoal for w msaux auxlist pos rel
    by (auto simp: valid_Leaf Let_def map_join_take_fill map_join_drop_fill map_join_fill[symmetric]
      join_distr plus_set_def rev_map[symmetric] map_snd_flip simp del: map_map
      dest!: valid_map_map_tree[where f="\<lambda>X. join X pos rel" and as = "replicate (earliest w) empty_table @ rev (map snd (drop (left (ivl w)) (fill auxlist)))", rotated])
  subgoal sorry
  subgoal for w msaux auxlist
    apply (auto split: option.splits if_splits simp: Let_def)
       apply (frule val_eq_Some_sum_if_valid_neq_Leaf)
        apply auto []
       apply (subst (asm) sum_alt)
         apply simp
        apply (unfold valid_def)
        apply (case_tac a)
         apply auto [2]
         apply (auto simp: rev_filter[symmetric] filter_map o_def nth_append empty_table_def plus_set_def zero_set_def split: if_split) []
       apply (simp add: foldr_conv_fold plus_set_def zero_set_def del: fold_simps)
       apply (erule arg_cong[where f="\<lambda>x. _ \<in> x", THEN iffD1, rotated])
       apply (rule arg_cong[where f="\<lambda>xs. fold (\<union>) (rev xs) {}"])
    apply (rule nth_equalityI)
        apply auto []
    find_theorems "concat (map _ _)"
    thm fold_plus_sum_list_rev
(*
    apply simp
      apply (auto dest!: val_eq_Some_sum_if_valid_neq_Leaf simp: nth_append
        rev_map[symmetric] foldr_conv_fold fold_plus_sum_list_rev split: if_splits)
*)
    find_theorems "fold (+)"
    sorry
  done
*)

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

lemma meval_MPred: "meval n t db (MPred e ts) = ([Option.these
  ((map_option (\<lambda>f. Table.tabulate f 0 n) o match ts) ` (\<Union>(e', x)\<in>db. if e = e' then {x} else {}))], MPred e ts)"
  unfolding default.meval.simps image_these image_image o_def ..

lemma meval_MPred': "meval n t db (MPred e ts) = ([Option.these
  (\<Union>(e', x)\<in>db. if e = e' then {map_option (\<lambda>f. Table.tabulate f 0 n) (match ts x)} else {})], MPred e ts)"
  unfolding meval_MPred image_UN split_beta if_distrib[of "image _"] image_insert image_empty o_apply
  ..

lemma these_UNION: "Option.these (\<Union>x \<in> A. B x) = (\<Union>x \<in> A. (Option.these o B) x)"
  by (auto simp: Option.these_def)

lemma meval_MPred'': "meval n t db (MPred e ts) = ([
  (\<Union>(e', x)\<in>db. if e = e' then set_option (map_option (\<lambda>f. Table.tabulate f 0 n) (match ts x)) else {})], MPred e ts)"
  unfolding meval_MPred' these_UNION o_def prod.case_distrib[of Option.these]
  by (auto simp: Option.these_def map_option_case image_iff split: if_splits option.splits)

lemmas meval_code[code] = default.meval.simps(1) meval_MPred'' default.meval.simps(3-13)

definition mk_db :: "(char list \<times> 'a list) list \<Rightarrow> (char list \<times> 'a list) set" where
  "mk_db = set"

definition rbt_verdict :: "_ \<Rightarrow> (nat \<times> 'a :: ccompare option list) list" where
  "rbt_verdict = RBT_Set2.keys"

definition rbt_multiset :: "_ \<Rightarrow> ('a :: ccompare \<times> enat) list" where
  "rbt_multiset = RBT_Set2.keys"

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
  and terminates: "mono g" "\<And>X. X \<subseteq> C \<Longrightarrow> g X \<subseteq> C" "finite C"
shows "saturate g {} = saturate h {r}"
proof (cases "g {} = {r}")
  case True
  with assms have "g {r} = {r}" "h {r} = {r}" by auto
  with True show ?thesis
    by (subst (1 2) saturate_code; subst saturate_code) (simp add: Let_def)
next
  case False
  then show ?thesis
    unfolding saturate_def while_def
    using while_option_finite_subset_Some[OF terminates] assms(1-3)
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "insert r" h "{}", symmetric])
      (auto 4 4 dest: while_option_stop[of "\<lambda>S. g S \<noteq> S" g "{}"])
qed

definition "RPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (RPD ` S))"

lemma RPDs_aux_code[code]:
  "RPDs_aux S = (let S' = S \<union> Set.bind S RPD in if S' \<subseteq> S then S else RPDs_aux S')"
  unfolding RPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare RPDs_code[code del]
lemma RPDs_code[code]: "RPDs r = RPDs_aux {r}"
  unfolding RPDs_aux_def RPDs_code
  by (rule saturate_commute[where C="RPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff RPDs_refl RPDs_trans finite_RPDs)

definition "LPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (LPD ` S))"

lemma LPDs_aux_code[code]:
  "LPDs_aux S = (let S' = S \<union> Set.bind S LPD in if S' \<subseteq> S then S else LPDs_aux S')"
  unfolding LPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare LPDs_code[code del]
lemma LPDs_code[code]: "LPDs r = LPDs_aux {r}"
  unfolding LPDs_aux_def LPDs_code
  by (rule saturate_commute[where C="LPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff LPDs_refl LPDs_trans finite_LPDs)

lemma is_empty_table_unfold [code_unfold]:
  "X = empty_table \<longleftrightarrow> Set.is_empty X"
  "empty_table = X \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set X empty_table \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set empty_table X \<longleftrightarrow> Set.is_empty X"
  "set_eq X empty_table \<longleftrightarrow> Set.is_empty X"
  "set_eq empty_table X \<longleftrightarrow> Set.is_empty X"
  unfolding set_eq_def empty_table_def Set.is_empty_def Cardinality.eq_set_def by auto

lemma tabulate_rbt_code[code]: "Monitor.mrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of None \<Rightarrow> Code.abort (STR ''tabulate RBT_Mapping: ccompare = None'') (\<lambda>_. Monitor.mrtabulate (xs :: mregex list) f)
  | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) xs)))"
  unfolding mrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

export_code convert_multiway minit_safe mstep
  checking OCaml?

export_code
  (*type classes*)
  HOL.equal Collection_Eq.ceq Collection_Order.ccompare set_impl
  (*basic types*)
  nat_of_integer integer_of_nat enat literal.explode interval mk_db RBT_set rbt_verdict rbt_multiset
  Eq phantom set_RBT
  (*term, formula, and regex constructors*)
  Formula.Var Formula.Pred Regex.Skip Regex.Wild
  (*main functions*)
  convert_multiway minit_safe mstep mmonitorable_exec
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
