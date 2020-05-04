theory Partitioned_Trace
  imports Trace "HOL-Library.BNF_Corec" "HOL-Library.DAList"
begin

notation fcomp (infixl "\<circ>>" 60)

definition determ :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "determ f = (\<lambda>x. {f x})"

lemma in_determ_iff_eq[simp]: "y \<in> determ f x \<longleftrightarrow> y = f x"
  by (simp add: determ_def)

definition kleisli_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'c set" where
  "kleisli_set f g = (\<lambda>x. Set.bind (f x) g)"

notation kleisli_set (infixl "\<circ>\<then>" 55)

lemma kleisli_set_assoc: "f \<circ>\<then> g \<circ>\<then> h = f \<circ>\<then> (g \<circ>\<then> h)"
  by (auto simp: kleisli_set_def Set.bind_def)

lemma determ_kleisli_set: "determ f \<circ>\<then> g = f \<circ>> g"
  by (auto simp: kleisli_set_def Set.bind_def determ_def)

lemma kleisli_set_mono: "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> f \<circ>\<then> g \<le> f' \<circ>\<then> g'"
  by (fastforce simp: le_fun_def kleisli_set_def Set.bind_def)

definition mapM_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> 'b list set" where
  "mapM_set f xs = listset (map f xs)"

lemma in_listset_iff: "xs \<in> listset As \<longleftrightarrow> list_all2 (\<in>) xs As"
  by (induction As arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma in_mapM_set_iff: "xs \<in> mapM_set f ys \<longleftrightarrow> list_all2 (\<lambda>x y. x \<in> f y) xs ys"
  by (simp add: mapM_set_def in_listset_iff list.rel_map)

lemma mapM_set_mono: "f \<le> f' \<Longrightarrow> mapM_set f \<le> mapM_set f'"
  by (fastforce simp: le_fun_def in_mapM_set_iff elim!: list.rel_mono_strong)

lemma mapM_set_determ: "mapM_set (determ f) = determ (map f)"
  by (auto simp: fun_eq_iff in_mapM_set_iff list.rel_map list.rel_map(2)[where g=f, symmetric]
      list.rel_eq intro!: list.rel_refl)

lemma kleisli_mapM_set: "mapM_set f \<circ>\<then> mapM_set g = mapM_set (f \<circ>\<then> g)"
  apply (auto simp: fun_eq_iff kleisli_set_def in_mapM_set_iff elim!: list_all2_trans[rotated])
  apply (simp add: Bex_def in_mapM_set_iff relcompp_apply)
  apply (insert list.rel_compp[where R="(\<lambda>x y. x \<in> f y)\<inverse>\<inverse>" and S="(\<lambda>x y. x \<in> g y)\<inverse>\<inverse>"])
  apply (simp add: relcompp_apply[abs_def] list.rel_flip fun_eq_iff)
  apply (drule spec)+
  apply (erule iffD1)
  by (simp add: list_all2_conv_all_nth)


record 'a itsdb =
  db :: "'a set"
  ts :: nat
  idx :: nat

typedef 'a itrace = "{s :: 'a itsdb stream.
  ssorted (smap idx s) \<and> sincreasing (smap ts s) \<and>
  (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j))}"
  by (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x\<rparr>) nats"])
    (auto simp: stream.map_comp stream.map_ident cong: stream.map_cong)

setup_lifting type_definition_itrace

lift_definition i\<Gamma> :: "'a itrace \<Rightarrow> nat \<Rightarrow> 'a set" is "\<lambda>s i. db (s !! i)" .
lift_definition i\<tau> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. ts (s !! i)" .
lift_definition i\<iota> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. idx (s !! i)" .

lift_definition map_i\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a itrace \<Rightarrow> 'b itrace" is
  "\<lambda>f. smap (\<lambda>x. \<lparr>db = f (db x), ts = ts x, idx = idx x\<rparr>)"
  by (simp add: stream.map_comp cong: stream.map_cong)

lemma i\<Gamma>_map_i\<Gamma>[simp]: "i\<Gamma> (map_i\<Gamma> f \<sigma>) i = f (i\<Gamma> \<sigma> i)"
  by transfer simp

lemma i\<tau>_map_i\<Gamma>[simp]: "i\<tau> (map_i\<Gamma> f \<sigma>) i = i\<tau> \<sigma> i"
  by transfer simp

lemma i\<iota>_map_i\<Gamma>[simp]: "i\<iota> (map_i\<Gamma> f \<sigma>) i = i\<iota> \<sigma> i"
  by transfer simp

lemma mono_i\<iota>: "i \<le> j \<Longrightarrow> i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j"
  by transfer (simp add: ssorted_iff_mono)

lemma i\<tau>_increasing: "\<exists>j>i. i\<tau> \<sigma> i < i\<tau> \<sigma> j"
  by transfer (simp add: sincreasing_def)

lemma i\<iota>_refines_i\<tau>: "i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j \<Longrightarrow> i\<tau> \<sigma> i \<le> i\<tau> \<sigma> j"
  by transfer simp

lemma mono_i\<tau>: "i \<le> j \<Longrightarrow> i\<tau> \<sigma> i \<le> i\<tau> \<sigma> j"
  using i\<iota>_refines_i\<tau>[OF mono_i\<iota>] .

lemma i\<iota>_not_stable: "\<exists>j>i. i\<iota> \<sigma> i \<noteq> i\<iota> \<sigma> j"
proof -
  obtain j where "i < j" and "i\<tau> \<sigma> i < i\<tau> \<sigma> j"
    using i\<tau>_increasing by blast
  moreover have "i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j"
    using \<open>i < j\<close> by (simp add: mono_i\<iota>)
  ultimately show ?thesis
    using i\<iota>_refines_i\<tau>[of \<sigma> j i] by auto
qed

lift_definition add_timepoints :: "'a trace \<Rightarrow> 'a itrace" is
  "smap2 (\<lambda>i (db, ts). \<lparr>db=db, ts=ts, idx=i\<rparr>) nats"
  by (auto simp: split_beta smap2_szip stream.map_comp smap_szip_fst[of id, simplified]
      stream.map_ident smap_szip_snd ssorted_iff_mono cong: stream.map_cong)

lift_definition add_timestamps :: "'a trace \<Rightarrow> 'a itrace" is
  "smap (\<lambda>(db, ts). \<lparr>db=db, ts=ts, idx=ts\<rparr>)"
  by (auto simp: split_beta stream.map_comp cong: stream.map_cong)

definition next_i\<iota> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" where
  "next_i\<iota> \<sigma> i = Inf {j. i < j \<and> i\<iota> \<sigma> i \<noteq> i\<iota> \<sigma> j}"

lemma Suc_le_next_i\<iota>: "Suc i \<le> next_i\<iota> \<sigma> i"
  using i\<iota>_not_stable by (auto simp: next_i\<iota>_def intro!: cInf_greatest)

lemma le_next_i\<iota>: "i \<le> next_i\<iota> \<sigma> i"
  using Suc_le_next_i\<iota> Suc_leD by blast

lemma mono_next_i\<iota>: "i \<le> i' \<Longrightarrow> next_i\<iota> \<sigma> i \<le> next_i\<iota> \<sigma> i'"
  unfolding next_i\<iota>_def
  apply (rule cInf_mono)
  using i\<iota>_not_stable apply auto
  by (metis le_eq_less_or_eq order.strict_trans)

definition collapse' :: "nat \<Rightarrow> 'a itrace \<Rightarrow> ('a set \<times> nat) stream" where
  "collapse' i0 \<sigma> = smap (\<lambda>i. (\<Union>i' \<in> i\<iota> \<sigma> -` {i\<iota> \<sigma> i}. i\<Gamma> \<sigma> i', i\<tau> \<sigma> i)) (siterate (next_i\<iota> \<sigma>) i0)"

lift_definition collapse :: "'a itrace \<Rightarrow> 'a trace" is "collapse' 0"
proof
  fix \<sigma> :: "'a itrace"
  have "ssorted (smap snd (collapse' i \<sigma>))" for i
    by (coinduction arbitrary: i) (auto simp: collapse'_def intro: mono_i\<tau> le_next_i\<iota>)
  then show "ssorted (smap snd (collapse' 0 \<sigma>))" .

  have "\<exists>k>j. smap snd (collapse' i \<sigma>) !! j < smap snd (collapse' i \<sigma>) !! k" for i j
  proof (induction j arbitrary: i)
    case 0
    obtain k where "i\<tau> \<sigma> i < i\<tau> \<sigma> k" using i\<tau>_increasing by blast
    moreover have "\<exists>k'. k \<le> (next_i\<iota> \<sigma> ^^ (Suc k')) i"
    proof (induction k)
      case 0
      show ?case by simp
    next
      case (Suc k)
      then obtain k' where "k \<le> (next_i\<iota> \<sigma> ^^ (Suc k')) i" ..
      then have "Suc k \<le> (next_i\<iota> \<sigma> ^^ (Suc (Suc k'))) i"
        by (auto intro: Suc_le_next_i\<iota>[THEN order_trans] mono_next_i\<iota>)
      then show ?case ..
    qed
    then have "\<exists>k'. i\<tau> \<sigma> k \<le> i\<tau> \<sigma> ((next_i\<iota> \<sigma> ^^ (Suc k')) i)"
      using mono_i\<tau> by blast
    ultimately show ?case
      by (auto simp add: collapse'_def simp del: funpow.simps elim: order.strict_trans2)
  next
    case (Suc j)
    from Suc.IH[of "next_i\<iota> \<sigma> i"] show ?case
      by (simp add: collapse'_def) (metis Suc_mono funpow.simps(2) funpow_swap1 o_apply)
  qed
  then show "sincreasing (smap snd (collapse' 0 \<sigma>))"
    by (simp add: sincreasing_def)
qed

lemma i\<Gamma>_timepoints[simp]: "i\<Gamma> (add_timepoints \<sigma>) = \<Gamma> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<tau>_timepoints[simp]: "i\<tau> (add_timepoints \<sigma>) = \<tau> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<iota>_timepoints[simp]: "i\<iota> (add_timepoints \<sigma>) = id"
  by transfer (simp add: split_beta id_def)

lemma next_i\<iota>_timepoints[simp]: "next_i\<iota> (add_timepoints \<sigma>) = Suc"
  by (fastforce simp: next_i\<iota>_def intro: antisym cInf_lower cInf_greatest)

lemma snth_Rep_trace: "Rep_trace \<sigma> !! i = (\<Gamma> \<sigma> i, \<tau> \<sigma> i)"
  by transfer simp

lemma add_timepoints_collapse: "add_timepoints \<circ>> collapse = id"
proof
  fix \<sigma> :: "'a trace"
  have "collapse' i (add_timepoints \<sigma>) = sdrop i (Rep_trace \<sigma>)" for i
    by (coinduction arbitrary: i) (auto simp: collapse'_def snth_Rep_trace)
  then show "(add_timepoints \<circ>> collapse) \<sigma> = id \<sigma>"
    by (intro Rep_trace_inject[THEN iffD1]) (simp add: collapse.rep_eq)
qed


locale itrace_partition =
  fixes \<sigma> :: "'a itrace" and n :: nat and ps :: "'a itrace list"
  assumes
    n_greater_0: "n > 0" and
    length_ps_eq_n: "length ps = n" and
    sound_partition: "\<forall>k<n. \<forall>j. \<exists>i. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> i\<Gamma> (ps ! k) j \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>k<n. \<exists>j. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> f \<in> i\<Gamma> (ps ! k) j"

definition partition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a itrace list set" where
  "partition n \<sigma> = {ps. itrace_partition \<sigma> n ps}"

primcorec sskip :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "sskip n s = (case s of x ## s' \<Rightarrow> x ## sskip n (sdrop n s'))"

lemma smap_sskip: "smap f (sskip n s) = sskip n (smap f s)"
  by (coinduction arbitrary: s) (auto simp: stream.case_eq_if)

lemma snth_sskip: "sskip n s !! i = s !! (i * Suc n)"
  by (induction i arbitrary: s)
    (simp_all add: stream.case_eq_if sdrop_snth ac_simps)

lemma ssorted_sskip: "ssorted s \<Longrightarrow> ssorted (sskip n s)"
  by (simp add: ssorted_iff_mono snth_sskip add_mono)

lemma sincreasing_sskip: "sincreasing s \<Longrightarrow> ssorted s \<Longrightarrow> sincreasing (sskip n s)"
  apply (auto simp add: sincreasing_def ssorted_iff_mono snth_sskip)
  subgoal for i
    apply (drule spec[of _ "i + i * n"])
    by (metis le_add1 le_less_trans not_le)
  done

lift_definition round_robin :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a itrace list" is
  "\<lambda>n s. map (\<lambda>k. sskip (n-1) (sdrop k s)) [0..<n]"
  apply (auto simp: list.pred_set smap_sskip snth_sskip sdrop_snth)
   apply (metis ssorted_sskip ssorted_sdrop sdrop_smap)
  apply (rule sincreasing_sskip)
   apply (subst sdrop_smap[symmetric])
   apply (erule sincreasing_sdrop)
  apply (subst sdrop_smap[symmetric])
  apply (rule ssorted_sdrop)
  apply (auto simp: ssorted_iff_mono)[]
  done

lemma length_round_robin[simp]: "length (round_robin n \<sigma>) = n"
  by transfer simp

lemma ix_round_robin:
  assumes "k < n"
  shows "i\<Gamma> (round_robin n \<sigma> ! k) j = i\<Gamma> \<sigma> (k + j * n)" and
    "i\<tau> (round_robin n \<sigma> ! k) j = i\<tau> \<sigma> (k + j * n)" and
    "i\<iota> (round_robin n \<sigma> ! k) j = i\<iota> \<sigma> (k + j * n)"
  using assms by (simp_all add: i\<Gamma>.rep_eq i\<tau>.rep_eq i\<iota>.rep_eq round_robin.rep_eq
      nth_map[where f=Rep_itrace, symmetric] snth_sskip sdrop_snth)

lemma round_robin_partition: "n > 0 \<Longrightarrow> round_robin n \<sigma> \<in> partition n \<sigma>"
  apply (simp add: partition_def)
  apply unfold_locales
      apply (auto simp: ix_round_robin Let_def)
  subgoal for i
    apply (rule exI[where x="i mod n"])
    apply simp
    apply (rule exI[where x="i div n"])
    apply (simp add: ix_round_robin)
    done
  subgoal for i
    apply (rule exI[where x="i mod n"])
    apply simp
    apply (rule exI[where x="i div n"])
    apply (simp add: ix_round_robin)
    done
  done


record 'a wtsdb = "'a itsdb" + wmark :: nat

definition wtracep :: "('a, 'b) wtsdb_scheme stream \<Rightarrow> bool" where
  "wtracep s \<longleftrightarrow> ssorted (smap wmark s) \<and> sincreasing (smap wmark s) \<and> sincreasing (smap ts s) \<and>
    (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j)) \<and>
    (\<forall>i. \<forall>j>i. wmark (s !! i) \<le> idx (s !! j))"

definition "dummy_raw_wtrace = smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x\<rparr>) nats"

lemma wtracep_dummy: "wtracep dummy_raw_wtrace"
  by (auto simp: wtracep_def dummy_raw_wtrace_def stream.map_comp stream.map_ident cong: stream.map_cong)

typedef 'a wtrace = "{s :: 'a wtsdb stream. wtracep s}"
  by (auto intro!: exI[where x=dummy_raw_wtrace] wtracep_dummy)

setup_lifting type_definition_wtrace

lift_definition w\<Gamma> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> 'a set" is "\<lambda>s i. db (s !! i)" .
lift_definition w\<tau> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. ts (s !! i)" .
lift_definition w\<iota> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. idx (s !! i)" .
lift_definition w\<beta> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. wmark (s !! i)" .

lift_definition map_w\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a wtrace \<Rightarrow> 'b wtrace" is
  "\<lambda>f. smap (\<lambda>x. \<lparr>db = f (db x), ts = ts x, idx = idx x, wmark = wmark x\<rparr>)"
  by (simp add: wtracep_def stream.map_comp cong: stream.map_cong)

lemma w\<Gamma>_map_w\<Gamma>[simp]: "w\<Gamma> (map_w\<Gamma> f \<sigma>) i = f (w\<Gamma> \<sigma> i)"
  by transfer simp

lemma w\<tau>_map_w\<Gamma>[simp]: "w\<tau> (map_w\<Gamma> f \<sigma>) i = w\<tau> \<sigma> i"
  by transfer simp

lemma w\<iota>_map_w\<Gamma>[simp]: "w\<iota> (map_w\<Gamma> f \<sigma>) i = w\<iota> \<sigma> i"
  by transfer simp

locale relaxed_order =
  fixes \<sigma> :: "'a itrace" and \<sigma>' :: "'a wtrace"
  assumes
    sound_reordering: "\<forall>j. \<exists>i. w\<iota> \<sigma>' j = i\<iota> \<sigma> i \<and> w\<tau> \<sigma>' j = i\<tau> \<sigma> i \<and> w\<Gamma> \<sigma>' j = i\<Gamma> \<sigma> i" and
    complete_reordering: "\<forall>i. \<exists>j. w\<iota> \<sigma>' j = i\<iota> \<sigma> i \<and> w\<tau> \<sigma>' j = i\<tau> \<sigma> i \<and> w\<Gamma> \<sigma>' j = i\<Gamma> \<sigma> i"

definition relax_order :: "'a itrace \<Rightarrow> 'a wtrace set" where
  "relax_order \<sigma> = {\<sigma>'. relaxed_order \<sigma> \<sigma>'}"

lift_definition id_wtrace :: "'a itrace \<Rightarrow> 'a wtrace" is
  "smap (\<lambda>x. \<lparr>db=db x, ts=ts x, idx=idx x, wmark=idx x\<rparr>)"
  by (simp add: wtracep_def stream.map_comp ssorted_iff_mono sincreasing_def cong: stream.map_cong)
    (meson not_le)

lemma id_wtrace_relax_order: "id_wtrace \<sigma> \<in> relax_order \<sigma>"
  by (simp add: relax_order_def relaxed_order_def) (transfer; auto)+


definition islice :: "('a \<Rightarrow> 'b set \<Rightarrow> 'c set) \<Rightarrow> 'a list \<Rightarrow> 'b itrace \<Rightarrow> 'c itrace list" where
  "islice f xs \<sigma> = map2 (\<lambda>x. map_i\<Gamma> (f x)) xs (replicate (length xs) \<sigma>)"

definition wslice :: "('a \<Rightarrow> 'b set \<Rightarrow> 'c set) \<Rightarrow> 'a list \<Rightarrow> 'b wtrace \<Rightarrow> 'c wtrace list" where
  "wslice f xs \<sigma> = map2 (\<lambda>x. map_w\<Gamma> (f x)) xs (replicate (length xs) \<sigma>)"

lemma map_w\<Gamma>_relax_order: "\<sigma>' \<in> relax_order \<sigma> \<Longrightarrow> map_w\<Gamma> f \<sigma>' \<in> relax_order (map_i\<Gamma> f \<sigma>)"
  by (fastforce simp: relax_order_def relaxed_order_def)

lemma relax_order_wslice:
  "(relax_order \<circ>\<then> determ (wslice f xs)) \<le> (islice f xs \<circ>> mapM_set relax_order)"
  by (auto simp: le_fun_def kleisli_set_def determ_def in_mapM_set_iff
      wslice_def islice_def in_set_zip intro!: list_all2I map_w\<Gamma>_relax_order)


lemma list_all2_transposeI: "list_all2 (list_all2 P) xss yss \<Longrightarrow> list_all2 (list_all2 P) (transpose xss) (transpose yss)"
  apply (rule list_all2_all_nthI)
  subgoal 1
    unfolding length_transpose
    by (induction xss yss pred: list_all2) (auto dest: list_all2_lengthD)
  subgoal for i
    apply (frule 1)
    apply (simp add: nth_transpose list.rel_map length_transpose)
    apply (thin_tac "_ < _")
    apply (thin_tac "_ = _")
    apply (induction xss yss pred: list_all2)
    apply (auto simp: list_all2_Cons1 dest: list_all2_nthD list_all2_lengthD)
    done
  done

lemma mapM_mapM_transpose:
  "(mapM_set (mapM_set f) \<circ>\<then> determ transpose) \<le> (transpose \<circ>> mapM_set (mapM_set f))"
  by (auto simp: le_fun_def kleisli_set_def in_mapM_set_iff intro!: list_all2_transposeI)


definition infinitely :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "infinitely P s \<longleftrightarrow> (\<forall>i. \<exists>j\<ge>i. P (s !! j))"

lemma infinitely_stl: "infinitely P (stl s) \<longleftrightarrow> infinitely P s"
  apply (auto simp: infinitely_def)
  apply (metis le_Suc_eq snth.simps(2))
  using Suc_le_D by fastforce

lemma infinitely_sset_stl: "infinitely P s \<Longrightarrow> \<exists>x \<in> sset (stl s). P x"
  by (fastforce simp: infinitely_def dest!: Suc_le_D)

lemma sdrop_while_id_conv: "stream_all P s \<Longrightarrow> sdrop_while (Not \<circ> P) s = s"
  by (subst sdrop_while_sdrop_LEAST) simp_all

lemma sfilter_id_conv: "stream_all P s \<Longrightarrow> sfilter P s = s"
  by (coinduction arbitrary: s) (auto simp: sdrop_while_id_conv stl_sset)

record 'a mwtsdb = "'a wtsdb" + origin :: nat

typedef 'a mwtrace = "{s :: 'a mwtsdb stream. finite (origin ` sset s) \<and>
  (\<forall>k \<in> origin ` sset s. infinitely (\<lambda>x. origin x = k) s \<and> wtracep (sfilter (\<lambda>x. origin x = k) s))}"
  apply (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats"])
  apply (auto simp: infinitely_def stream.set_map image_image)
  apply (subst sfilter_id_conv)
   apply (simp add: stream.set_map)
  apply (auto simp: wtracep_def stream.map_comp stream.map_ident cong: stream.map_cong)
  done

setup_lifting type_definition_mwtrace

lemma wtracep_stlI: "wtracep s \<Longrightarrow> wtracep (stl s)"
  apply (auto simp: wtracep_def sincreasing_def elim: ssorted.cases)
     apply (metis Suc_leI Suc_le_D Suc_le_lessD less_Suc_eq_le snth.simps(2))
    apply (metis Suc_leI Suc_le_D Suc_le_lessD less_Suc_eq_le snth.simps(2))
   apply (metis snth.simps(2))
  by (metis Suc_mono snth.simps(2))

lemma sfilter_stl_cases:
  obtains "P (shd s)" "sfilter P (stl s) = stl (sfilter P s)" |
    "\<not> P (shd s)" "sfilter P (stl s) = sfilter P s"
  by (cases s) (auto simp: sfilter_Stream)

lift_definition mwnth :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> 'a mwtsdb" is snth .
lift_definition mwhd :: "'a mwtrace \<Rightarrow> 'a mwtsdb" is shd .
lift_definition mwtl :: "'a mwtrace \<Rightarrow> 'a mwtrace" is stl
  apply (auto 0 3 simp: infinitely_stl intro: stl_sset elim: finite_subset[rotated])
  subgoal for s x
    by (rule sfilter_stl_cases[of "\<lambda>y. origin y = origin x" s])
      (auto simp del: sfilter.simps intro!: wtracep_stlI stl_sset)
  done

lemma mwnth_zero: "mwnth \<sigma> 0 = mwhd \<sigma>"
  by transfer simp

lemma mwnth_Suc: "mwnth \<sigma> (Suc i) = mwnth (mwtl \<sigma>) i"
  by transfer simp

lift_definition mworigins :: "'a mwtrace \<Rightarrow> nat set" is "\<lambda>s. origin ` sset s" .

lemma mworigins_not_empty[simp]: "mworigins \<sigma> \<noteq> {}"
  by transfer (simp add: sset_range)

lemma finite_mworigins[simp]: "finite (mworigins \<sigma>)"
  by transfer simp

lemma origin_mwhd: "origin (mwhd \<sigma>) \<in> mworigins \<sigma>"
  by transfer (simp add: shd_sset)

lemma origin_mwnth: "origin (mwnth \<sigma> i) \<in> mworigins \<sigma>"
  by transfer simp

lemma mworigins_mwtl: "mworigins (mwtl \<sigma>) = mworigins \<sigma>"
  apply transfer
  apply (auto intro: stl_sset)
  apply (drule (1) bspec)
  apply clarify
  apply (drule infinitely_sset_stl)
  by (metis imageI)

lift_definition dummy_mwtrace :: "'a mwtrace" is "smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats"
  by (auto simp: stream.set_map image_image infinitely_def sfilter_id_conv
      wtracep_def stream.map_comp stream.map_ident cong: stream.map_cong)

lemma mworigins_dummy: "mworigins dummy_mwtrace = {0}"
  by transfer (simp add: stream.set_map image_image)

lemma wtracep_smap_truncate: "wtracep (smap wtsdb.truncate s) \<longleftrightarrow> wtracep s"
  by (simp add: wtracep_def stream.map_comp wtsdb.truncate_def cong: stream.map_cong)

lift_definition mwproject :: "nat \<Rightarrow> 'a mwtrace \<Rightarrow> 'a wtrace" is
  "\<lambda>k s. if k \<in> origin ` sset s then smap wtsdb.truncate (sfilter (\<lambda>x. origin x = k) s)
    else dummy_raw_wtrace"
  by (auto simp: wtracep_smap_truncate wtracep_dummy)

definition linearize :: "'a wtrace list \<Rightarrow> 'a mwtrace set" where
  "linearize \<sigma>s = {\<sigma>. mworigins \<sigma> = {..<length \<sigma>s} \<and> (\<forall>k < length \<sigma>s. mwproject k \<sigma> = \<sigma>s ! k)}"

(* TODO(JS): Show that linearize \<sigma> is not empty. *)


record 'a raw_reorder_state =
  wmarks :: "(nat, nat) alist"
  buffer :: "(nat, ('a set \<times> nat)) alist"

definition reorder_update :: "'a mwtsdb \<Rightarrow> 'a raw_reorder_state \<Rightarrow> 'a raw_reorder_state" where
  "reorder_update x st = \<lparr>wmarks = DAList.update (origin x) (wmark x) (wmarks st),
    buffer = DAList.map_default (idx x) (db x, ts x) (\<lambda>(d, t). (d \<union> db x, t)) (buffer st)\<rparr>"

definition reorder_flush :: "'a raw_reorder_state \<Rightarrow> ('a set \<times> nat) list \<times> 'a raw_reorder_state" where
  "reorder_flush st = (let w = Min (alist.set (wmarks st)) in
    (map snd (sort_key fst (filter (\<lambda>x. fst x < w) (DAList.impl_of (buffer st)))),
      st\<lparr>buffer := DAList.filter (\<lambda>x. fst x \<ge> w) (buffer st)\<rparr>))"

lift_definition keyset :: "('a, 'b) alist \<Rightarrow> 'a set" is "\<lambda>xs. fst ` set xs" .

lemma keyset_empty[simp]: "keyset DAList.empty = {}"
  by transfer simp

lemma keyset_update[simp]: "keyset (DAList.update k v al) = insert k (keyset al)"
  by transfer (simp add: dom_update)

typedef 'a reorder_state = "{(st :: 'a raw_reorder_state, \<sigma> :: 'a mwtrace).
  keyset (wmarks st) = mworigins \<sigma> \<and> (\<forall>i \<in> keyset (buffer st). Min (alist.set (wmarks st)) \<le> i) \<and>
  (\<forall>k \<in> mworigins \<sigma>. \<forall>i. the (DAList.lookup (wmarks st) k) \<le> w\<iota> (mwproject k \<sigma>) i) \<and>
  (\<forall>k \<in> mworigins \<sigma>. \<forall>i. the (DAList.lookup (wmarks st) k) \<le> w\<beta> (mwproject k \<sigma>) i)}"
  by (rule exI[where x="(\<lparr>wmarks=DAList.update 0 0 DAList.empty, buffer=DAList.empty\<rparr>, dummy_mwtrace)"])
    (simp add: mworigins_dummy)

setup_lifting type_definition_reorder_state

lemma mwproject_mwtl: "origin (mwhd \<sigma>) \<noteq> k \<Longrightarrow> mwproject k (mwtl \<sigma>) = mwproject k \<sigma>"
  apply transfer
  apply (auto dest: stl_sset)
  subgoal for \<sigma> x x' by (cases \<sigma>) (simp add: sfilter_Stream)
  by (metis image_eqI insert_iff stream.collapse stream.simps(8))

lemma wmark_mwhd_le_w\<iota>: "wmark (mwhd \<sigma>) \<le> w\<iota> (mwproject (origin (mwhd \<sigma>)) (mwtl \<sigma>)) i"
  apply (transfer fixing: i)
  apply auto
  subgoal for \<sigma> x
    apply (auto simp: wtracep_def wtsdb.defs dest!: stl_sset)
    apply (drule (1) bspec)
    apply clarify
    apply (drule spec[of "\<lambda>i. \<forall>j. i < j \<longrightarrow> _ i j" 0])
    apply (drule spec[of "\<lambda>j. 0 < j \<longrightarrow> _ j" "Suc i"])
    apply (simp add: sdrop_while.simps)
    done
  subgoal using image_iff infinitely_sset_stl shd_sset by fastforce
  done

lemma wmark_mwhd_le_w\<beta>: "wmark (mwhd \<sigma>) \<le> w\<beta> (mwproject (origin (mwhd \<sigma>)) (mwtl \<sigma>)) i"
  apply (transfer fixing: i)
  apply auto
  subgoal for \<sigma> x
    apply (auto simp: wtracep_def wtsdb.defs dest!: stl_sset)
    apply (drule (1) bspec)
    apply clarify
    apply (drule ssorted_monoD[where i=0 and j="Suc i"])
     apply (simp_all add: sdrop_while.simps)
    done
  subgoal using image_iff infinitely_sset_stl shd_sset by fastforce
  done

lemma keyset_filter_impl: "keyset (DAList.filter P al) = fst ` (set (filter P (DAList.impl_of al)))"
  by transfer simp

lift_definition reorder_step :: "'a reorder_state \<Rightarrow> ('a set \<times> nat) list \<times> 'a reorder_state" is
  "\<lambda>(st, \<sigma>). let (xs, st') = reorder_flush (reorder_update (mwhd \<sigma>) st) in (xs, (st', mwtl \<sigma>))"
  by (auto simp: split_beta Let_def reorder_update_def reorder_flush_def origin_mwhd mworigins_mwtl
      lookup_update mwproject_mwtl wmark_mwhd_le_w\<iota> wmark_mwhd_le_w\<beta> keyset_filter_impl)

friend_of_corec shift :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "shift xs s = (case xs of [] \<Rightarrow> shd s | x # _ \<Rightarrow> x) ## (case xs of [] \<Rightarrow> stl s | _ # ys \<Rightarrow> shift ys s)"
  subgoal by (simp split: list.split)
  subgoal by transfer_prover
  done

definition next_to_emit :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> nat" where
  "next_to_emit st \<sigma> = (if buffer st = DAList.empty then idx (mwhd \<sigma>) else Min (keyset (buffer st)))"

definition next_to_release :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "next_to_release st \<sigma> k = (if next_to_emit st \<sigma> < the (DAList.lookup (wmarks st) k) then 0
    else Suc (LEAST i. origin (mwnth \<sigma> i) = k \<and> next_to_emit st \<sigma> < wmark (mwnth \<sigma> i)))"

lift_definition reorder_variant :: "'a reorder_state \<Rightarrow> nat" is
  "\<lambda>(st, \<sigma>). Max (next_to_release st \<sigma> ` keyset (wmarks st))" .

lemma sort_key_empty_conv: "sort_key f xs = [] \<longleftrightarrow> xs = []"
  by (induction xs) simp_all

lemma DAList_filter_id_conv: "DAList.filter P al = al \<longleftrightarrow> (\<forall>x \<in> set (DAList.impl_of al). P x)"
  by (transfer fixing: P) (rule filter_id_conv)

lemma alist_set_impl: "alist.set al = snd ` set (DAList.impl_of al)"
  by transfer force

lemma finite_keyset[simp]: "finite (keyset al)"
  by (simp add: keyset.rep_eq)

lemma finite_alist_set[simp]: "finite (alist.set al)"
  by (simp add: alist_set_impl)

lemma alist_set_empty_conv: "alist.set al = {} \<longleftrightarrow> keyset al = {}"
  by (simp add: alist_set_impl keyset.rep_eq)

lemma keyset_empty_eq_conv: "keyset al = {} \<longleftrightarrow> al = DAList.empty"
  by transfer simp

lemma in_alist_set_conv: "x \<in> alist.set al \<longleftrightarrow> (\<exists>k \<in> keyset al. DAList.lookup al k = Some x)"
  by (transfer fixing: x) force

lemma lookup_in_alist_set: "k \<in> keyset al \<Longrightarrow> the (DAList.lookup al k) \<in> alist.set al"
  by (transfer fixing: k) force

lemma keyset_map_default: "keyset (DAList.map_default k v f al) = insert k (keyset al)"
  by (transfer fixing: k v f) (simp add: dom_map_default)

lemma map_default_neq_empty[simp]: "DAList.map_default k v f al \<noteq> DAList.empty"
  apply (transfer fixing: k v f)
  subgoal for xs
    by (induction xs) simp_all
  done

lemma w\<beta>_mwproject_mwhd: "w\<beta> (mwproject (origin (mwhd \<sigma>)) \<sigma>) 0 = wmark (mwhd \<sigma>)"
  apply transfer
  subgoal for \<sigma>
    by (cases \<sigma>) (auto simp: wtsdb.defs sfilter_Stream)
  done

lemma Least_less_Least: "\<exists>x::'a::wellorder. Q x \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> \<exists>y. P y \<and> y < x) \<Longrightarrow> Least P < Least Q"
  by (metis LeastI2 less_le_trans not_le_imp_less not_less_Least)

lemma sincreasing_ex_greater: "sincreasing s \<Longrightarrow> \<exists>i\<ge>j. (x::nat) < s !! i"
  unfolding sincreasing_def
  apply (induction x)
   apply simp_all
   apply (meson dual_order.strict_implies_order less_eq_nat.simps(1) order.strict_trans1)
  by (meson less_trans_Suc order.order_iff_strict order.trans)

lemma infinitely_exists: "infinitely P s \<Longrightarrow> \<exists>i. P (s !! i)"
  by (auto simp: infinitely_def)

lemma infinitely_sdrop: "infinitely P s \<Longrightarrow> infinitely P (sdrop n s)"
  apply (auto simp add: infinitely_def sdrop_snth)
  subgoal for i
    apply (drule spec[of _ "i + n"])
    apply clarify
    subgoal for j by (rule exI[of _ "j - n"]) simp
    done
  done

lemma snth_sfilter: "infinitely P s \<Longrightarrow> \<exists>j. sfilter P s !! i = s !! j \<and> P (s !! j)"
  apply (induction i arbitrary: s)
   apply (simp add: sdrop_while_sdrop_LEAST infinitely_exists)
  using LeastI_ex infinitely_exists apply force
  apply (simp add: sdrop_while_sdrop_LEAST infinitely_exists)
  subgoal for i s
    apply (drule meta_spec)
    apply (drule meta_mp)
     apply (rule infinitely_sdrop[where n="LEAST n. P (s !! n)"])
     apply (erule infinitely_stl[THEN iffD2])
    apply (clarsimp simp add: sdrop_snth snth.simps(2)[symmetric] simp del: snth.simps(2))
    apply (rule exI)
    apply (rule conjI[OF refl])
    apply assumption
    done
  done

lemma ex_wmark_greater: "k \<in> mworigins \<sigma> \<Longrightarrow> \<exists>i. origin (mwnth \<sigma> i) = k \<and> w < wmark (mwnth \<sigma> i)"
  apply (transfer fixing: k w)
  apply (clarsimp simp: wtracep_def)
  subgoal for \<sigma> x
    apply (drule (1) bspec)
    apply clarify
    apply (drule sincreasing_ex_greater[where s="smap wmark _" and x=w])
    apply clarify
    subgoal for i
      apply (frule snth_sfilter[where i=i])
      apply auto
      done
    done
  done

lemma reorder_termination: "fst (reorder_step st) = [] \<Longrightarrow>
  reorder_variant (snd (reorder_step st)) < reorder_variant st"
  apply transfer
  apply (clarsimp split: prod.splits)
  subgoal premises assms for st \<sigma> st'
  proof -
    note step_eq = \<open>_ = ([], st')\<close>
    note w\<beta>_inv = \<open>\<forall>k\<in>mworigins \<sigma>. \<forall>i. the (DAList.lookup (wmarks st) k) \<le> w\<beta> (mwproject k \<sigma>) i\<close>
    let ?x = "mwhd \<sigma>"
    let ?st1 = "reorder_update ?x st"

    have [simp]: "keyset (wmarks st) \<noteq> {}"
      using \<open>keyset (wmarks st) = mworigins \<sigma>\<close> by simp

    have 1: "wmarks (reorder_update ?x st) = DAList.update (origin ?x) (wmark ?x) (wmarks st)"
      by (simp add: reorder_update_def)
    then have wmarks_st': "wmarks st' = \<dots>"
      using step_eq by (auto simp: reorder_flush_def Let_def)
    then have "keyset (wmarks st') = mworigins \<sigma>"
      using \<open>keyset (wmarks st) = mworigins \<sigma>\<close>
      by (simp add: insert_absorb origin_mwhd)

    from 1 have Min_wmarks_st1: "Min (alist.set (wmarks ?st1)) \<ge> Min (alist.set (wmarks st))"
      apply (clarsimp simp: alist_set_empty_conv Min_le_iff in_alist_set_conv)
      subgoal for w
        apply (cases "w = wmark (mwhd \<sigma>)")
        subgoal
          apply simp
          apply (rule bexI[where x="the (DAList.lookup (wmarks st) (origin (mwhd \<sigma>)))"])
           apply (rule w\<beta>_inv[THEN bspec[of _ _ "origin (mwhd \<sigma>)"], OF origin_mwhd, THEN spec[of _ 0],
                simplified w\<beta>_mwproject_mwhd])
          apply (auto simp: \<open>keyset (wmarks st) = mworigins \<sigma>\<close> origin_mwhd intro!: lookup_in_alist_set)
          done
        apply (auto 0 3 simp: lookup_update in_alist_set_conv split: if_splits intro: bexI[where x=w])
        done
      done

    have buffer_st'_eq: "buffer st' = buffer (reorder_update ?x st)"
      using step_eq
      by (auto simp: reorder_flush_def Let_def sort_key_empty_conv filter_empty_conv
          DAList_filter_id_conv not_less)
    have buffer_st1_eq: "buffer (reorder_update ?x st) =
      DAList.map_default (idx ?x) (db ?x, ts ?x) (\<lambda>(d, t). (d \<union> db ?x, t)) (buffer st)"
      by (simp add: reorder_update_def)

    have "\<forall>i \<in> keyset (buffer ?st1). Min (alist.set (wmarks ?st1)) \<le> i"
      using step_eq
      by (simp add: reorder_flush_def Let_def sort_key_empty_conv filter_empty_conv
          keyset.rep_eq not_less)
    then have "\<forall>i \<in> keyset (buffer ?st1). Min (alist.set (wmarks st)) \<le> i"
      using Min_wmarks_st1 by auto
    then have "Min (alist.set (wmarks st)) \<le> next_to_emit st \<sigma>"
      by (auto simp: buffer_st1_eq keyset_map_default next_to_emit_def keyset_empty_eq_conv)
    then obtain k1 where
      "k1 \<in> mworigins \<sigma>" and
      "the (DAList.lookup (wmarks st) k1) \<le> next_to_emit st \<sigma>"
      by (auto simp: Min_le_iff alist_set_empty_conv in_alist_set_conv
          \<open>keyset (wmarks st) = mworigins \<sigma>\<close>)
    then have next_k1: "next_to_release st \<sigma> k1 > 0"
      by (simp add: next_to_release_def)

    have next_st': "next_to_emit st' (mwtl \<sigma>) \<le> next_to_emit st \<sigma>"
      by (auto simp: next_to_emit_def buffer_st'_eq buffer_st1_eq keyset_map_default
          keyset_empty_eq_conv intro!: Min_antimono)

    have "\<exists>k' \<in> mworigins \<sigma>. next_to_release st' (mwtl \<sigma>) k < next_to_release st \<sigma> k'"
      if "k \<in> mworigins \<sigma>" for k
    proof (cases "next_to_release st \<sigma> k")
      case 0
      note next_st'
      also have "next_to_emit st \<sigma> < the (DAList.lookup (wmarks st) k)"
        using 0 by (simp add: next_to_release_def split: if_splits)
      also have "\<dots> \<le> the (DAList.lookup (wmarks st') k)"
        by (clarsimp simp: wmarks_st' lookup_update
            intro!: w\<beta>_inv[THEN bspec[of _ _ "origin (mwhd \<sigma>)"], OF origin_mwhd, THEN spec[of _ 0],
              simplified w\<beta>_mwproject_mwhd])
      finally have "next_to_release st' (mwtl \<sigma>) k = 0"
        by (simp add: next_to_release_def)
      then show ?thesis using next_k1 \<open>k1 \<in> mworigins \<sigma>\<close> by auto
    next
      let ?least = "\<lambda>st \<sigma>. (LEAST i. origin (mwnth \<sigma> i) = k \<and> next_to_emit st \<sigma> < wmark (mwnth \<sigma> i))"
      case (Suc i)
      then have i_eq: "i = ?least st \<sigma>"
        by (simp add: next_to_release_def split: if_splits)
      have 1: "?least st' (mwtl \<sigma>) < ?least st \<sigma>"
        if *: "next_to_emit st' (mwtl \<sigma>) \<ge> the (DAList.lookup (wmarks st') k)"
      proof (rule Least_less_Least[OF ex_wmark_greater, OF \<open>k \<in> mworigins \<sigma>\<close>], safe)
        fix j
        assume "next_to_emit st \<sigma> < wmark (mwnth \<sigma> j)" "k = origin (mwnth \<sigma> j)"
        then have **: "next_to_emit st' (mwtl \<sigma>) < wmark (mwnth \<sigma> j)"
          using next_st' by (elim order.strict_trans1)
        have "j \<noteq> 0" proof
          assume "j = 0"
          then have "the (DAList.lookup (wmarks st') k) = wmark (mwnth \<sigma> 0)"
            using \<open>k = origin (mwnth \<sigma> j)\<close>
            by (simp add: wmarks_st' lookup_update mwnth_zero)
          with * ** show False by (simp add: \<open>j = 0\<close>)
        qed
        then obtain i where "j = Suc i" by (cases j) simp_all
        then show "\<exists>i. (origin (mwnth (mwtl \<sigma>) i) = origin (mwnth \<sigma> j) \<and>
              next_to_emit st' (mwtl \<sigma>) < wmark (mwnth (mwtl \<sigma>) i)) \<and> i < j"
          using ** by (auto simp: mwnth_Suc)
      qed
      show ?thesis
        apply (rule bexI[OF _ \<open>k \<in> mworigins \<sigma>\<close>])
        apply (simp add: Suc)
        apply (simp add: next_to_release_def i_eq not_less 1)
        done
    qed
    then show ?thesis
      unfolding \<open>keyset (wmarks st') = mworigins \<sigma>\<close>
      by simp (auto simp: Max_gr_iff \<open>keyset (wmarks st') = mworigins \<sigma>\<close>)
  qed
  done

corecursive reorder :: "'a reorder_state \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder st = (let (xs, st') = reorder_step st in
    case xs of
      [] \<Rightarrow> reorder st'
    | x # xs' \<Rightarrow> x ## xs' @- reorder st')"
  by (relation "measure reorder_variant") (simp_all add: reorder_termination)

lift_definition init_alist :: "'a::linorder set \<Rightarrow> 'b \<Rightarrow> ('a, 'b) alist" is
  "\<lambda>K v. if finite K then map (\<lambda>k. (k, v)) (sorted_list_of_set K) else []"
  by (simp cong: map_cong)

lemma keyset_init_alist: "finite K \<Longrightarrow> keyset (init_alist K v) = K"
  by transfer (simp add: image_image)

lemma lookup_init_alist: "finite K \<Longrightarrow> k \<in> K \<Longrightarrow> DAList.lookup (init_alist K v) k = Some v"
  by transfer (simp add: map_of_map_restrict)

lift_definition init_reorder_state :: "'a mwtrace \<Rightarrow> 'a reorder_state" is
  "\<lambda>\<sigma>. (\<lparr>wmarks = init_alist (mworigins \<sigma>) 0, buffer = DAList.empty\<rparr>, \<sigma>)"
  by (simp add: keyset_init_alist lookup_init_alist)

definition reorder' :: "'a mwtrace \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder' \<sigma> = reorder (init_reorder_state \<sigma>)"


definition least_idx :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "least_idx \<sigma> i0 = (LEAST i. i0 \<le> i \<and> (\<exists>j. i = idx (mwnth \<sigma> j)))"

definition idx_stream :: "'a mwtrace \<Rightarrow> nat stream" where
  "idx_stream \<sigma> = siterate (least_idx \<sigma> \<circ> Suc) (least_idx \<sigma> 0)"

definition collapse_idx :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> 'a set" where
  "collapse_idx \<sigma> i = (\<Union>{d. \<exists>j. i = idx (mwnth \<sigma> j) \<and> d = db (mwnth \<sigma> j)})"

definition ts_of_idx :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "ts_of_idx \<sigma> i = ts (mwnth \<sigma> (LEAST j. i = idx (mwnth \<sigma> j)))"

definition reorder_alt :: "'a mwtrace \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder_alt \<sigma> = smap (\<lambda>i. (collapse_idx \<sigma> i, ts_of_idx \<sigma> i)) (idx_stream \<sigma>)"

definition collapse_reorder_state :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow>  (nat \<times> 'a set \<times> nat) set" where
  "collapse_reorder_state st \<sigma>' =
    {(i, (d \<union> (collapse_idx \<sigma>' i), t)) | i d t. (i, (d, t)) \<in> set (DAList.impl_of (buffer st))} \<union>
    {(i, (collapse_idx \<sigma>' i, ts_of_idx \<sigma>' i)) | i. i \<notin> keyset (buffer st) \<and> (\<exists>j. i = idx (mwnth \<sigma>' j))}"

lift_definition reorder_state_rel :: "'a mwtrace \<Rightarrow> 'a reorder_state \<Rightarrow> nat \<Rightarrow> bool" is
  "\<lambda>\<sigma> (st, \<sigma>') n. collapse_reorder_state st \<sigma>' = {(i, collapse_idx \<sigma> i, ts_of_idx \<sigma> i) | i. i \<in> sset (sdrop n (idx_stream \<sigma>))}" .

lemma ex_idx_ge: "\<exists>x\<ge>y. \<exists>j. x = idx (mwnth \<sigma> j)"
  apply (transfer fixing: y)
  subgoal for \<sigma>
    apply (clarsimp simp: wtracep_def)
    apply (drule bspec[where x="shd \<sigma>"])
     apply (simp add: shd_sset)
    apply clarify
    apply (drule sincreasing_ex_greater[where x=y])
    apply (thin_tac "\<forall>i j. _ i j")
    apply clarsimp
    subgoal for i
      apply (drule spec)+
      apply (drule mp)
       apply (rule lessI[of i])
      apply (drule (1) order.strict_trans2)
      by (metis order.order_iff_strict snth_sfilter)
    done
  done

lemma sset_idx_stream: "sset (idx_stream \<sigma>) = {i. \<exists>j. i = idx (mwnth \<sigma> j)}"
  apply (auto simp: idx_stream_def sset_siterate)
  subgoal for n
    apply (induction n)
     apply (simp add: least_idx_def)
     apply (rule LeastI)
     apply blast
    apply clarsimp
    subgoal for n j
    apply (thin_tac _)
    apply (simp add: least_idx_def)
      apply (insert LeastI_ex[where P="\<lambda>i. Suc (idx (mwnth \<sigma> j)) \<le> i \<and> (\<exists>j. i = idx (mwnth \<sigma> j))"])
      apply (drule meta_mp)
      apply (rule ex_idx_ge)
      apply simp
      done
    done
  subgoal for j proof -
    have "\<And>i'. i' \<le> i \<Longrightarrow> \<exists>j. i' = idx (mwnth \<sigma> j) \<Longrightarrow>
      \<exists>n. i' = ((least_idx \<sigma> \<circ> Suc) ^^ n) (least_idx \<sigma> 0)" for i
      apply (induction i)
       apply (auto simp: least_idx_def intro!: exI[where x=0])[]
      subgoal for i i'
        apply (cases "i' = Suc i"; simp)
        apply (cases "\<exists>i''. i'' \<le> i \<and> (\<exists>j. i'' = idx (mwnth \<sigma> j))")
        subgoal
          apply clarsimp
          apply (drule meta_spec[where x="GREATEST i''. i'' \<le> i \<and> (\<exists>j. i'' = idx (mwnth \<sigma> j))"])
          apply (drule meta_mp)
           apply (metis (mono_tags, lifting) GreatestI_ex_nat)
          apply (drule meta_mp)
           apply (smt GreatestI_ex_nat)
          apply clarify
          subgoal for j j' n
            apply (rule exI[where x="Suc n"])
            apply (clarsimp simp: least_idx_def)
            apply (rule Least_equality[symmetric])
             apply (smt GreatestI_nat not_less_eq_eq)
            by (metis (mono_tags, lifting) Greatest_le_nat not_less_eq_eq)
          done
        subgoal
          apply (rule exI[where x=0])
          apply (auto simp: least_idx_def)
          by (smt Least_equality less_Suc_eq_le not_less)
        done
      done
    then show ?thesis by auto
  qed
  done

lemma reorder_state_rel_init: "reorder_state_rel \<sigma> (init_reorder_state \<sigma>) 0"
  by transfer (simp add: collapse_reorder_state_def DAList.empty.rep_eq sset_idx_stream)

lemma set_map_default: "set (DAList.impl_of (DAList.map_default k v f al)) =
  {case DAList.lookup al k of None \<Rightarrow> (k, v) | Some v' \<Rightarrow> (k, f v')} \<union>
  {x. x \<in> set (DAList.impl_of al) \<and> fst x \<noteq> k}"
  apply (transfer fixing: k v f)
  subgoal for xs by (induction xs) (auto simp: image_iff)
  done

lemma lookup_None_set_conv: "DAList.lookup al k = None \<longleftrightarrow> k \<notin> fst ` set (DAList.impl_of al)"
  by (transfer fixing: k) (simp add: map_of_eq_None_iff)

lemma lookup_Some_set_conv: "DAList.lookup al k = Some v \<longleftrightarrow> (k, v) \<in> set (DAList.impl_of al)"
  by (transfer fixing: k v) simp

lemma collapse_idx_mwtl: "collapse_idx \<sigma> i =
  (if i = idx (mwhd \<sigma>) then db (mwhd \<sigma>) \<union> collapse_idx (mwtl \<sigma>) i else collapse_idx (mwtl \<sigma>) i)"
  apply (auto simp: collapse_idx_def)
      apply (metis mwnth_Suc mwnth_zero not0_implies_Suc)
     apply (metis mwnth_zero)
    apply (metis mwnth_Suc)
   apply (metis mwnth_Suc mwnth_zero not0_implies_Suc)
  apply (metis mwnth_Suc)
  done

lemma ts_of_idx_mwtl: "(\<exists>j. i = idx (mwnth \<sigma> j)) \<Longrightarrow> ts_of_idx \<sigma> i =
  (if i = idx (mwhd \<sigma>) then ts (mwhd \<sigma>) else ts_of_idx (mwtl \<sigma>) i)"
  apply (auto simp: ts_of_idx_def mwnth_zero)
  apply (subgoal_tac "(LEAST j. i = idx (mwnth \<sigma> j)) = Suc (LEAST j. i = idx (mwnth (mwtl \<sigma>) j))")
   apply (simp add: mwnth_Suc)
  apply simp
  apply (subst mwnth_Suc[symmetric])
  apply (rule Least_Suc[OF refl])
  apply (simp add: mwnth_zero)
  done

lemma alist_eq_key_imp_eq: "(k, v) \<in> set (DAList.impl_of al) \<Longrightarrow> (k, v') \<in> set (DAList.impl_of al) \<Longrightarrow> v = v'"
  by (transfer fixing: k v v') (simp add: eq_key_imp_eq_value)

lemma reorder_state_rel_step: "reorder_state_rel \<sigma> st n \<Longrightarrow>
  reorder_step st = (xs, st') \<Longrightarrow> xs = stake (length xs) (sdrop n (reorder_alt \<sigma>)) \<and>
    reorder_state_rel \<sigma> st' (n + length xs)"
  apply (transfer fixing: \<sigma> n xs)
  apply (clarsimp split: prod.splits)
  subgoal premises assms for st \<sigma>' st'
  proof -
    note old_state = \<open>collapse_reorder_state st \<sigma>' =
      {(i, collapse_idx \<sigma> i, ts_of_idx \<sigma> i) |i. i \<in> sset (sdrop n (idx_stream \<sigma>))}\<close>
    note step_eq = \<open>_ = (xs, st')\<close>
    let ?x = "mwhd \<sigma>'"
    let ?st1 = "reorder_update ?x st"

    have buffer_st1: "buffer ?st1 =
      DAList.map_default (idx ?x) (db ?x, ts ?x) (\<lambda>(d, t). (d \<union> db ?x, t)) (buffer st)"
      by (simp add: reorder_update_def)

    have 1: "{(i, collapse_idx \<sigma>' i, ts_of_idx \<sigma>' i) |i. i \<notin> keyset (buffer st) \<and> (\<exists>j. i = idx (mwnth \<sigma>' j))} =
      {(i, collapse_idx \<sigma>' i, if i = idx (mwhd \<sigma>') then ts (mwhd \<sigma>') else ts_of_idx (mwtl \<sigma>') i) |
        i. i \<notin> keyset (buffer st) \<and> (\<exists>j. i = idx (mwnth \<sigma>' j))}"
      by (simp only: ts_of_idx_mwtl cong: rev_conj_cong)
    have 2: "(\<exists>j. i = idx (mwnth \<sigma>' j)) \<longleftrightarrow> i = idx (mwhd \<sigma>') \<or> (\<exists>j. i = idx (mwnth (mwtl \<sigma>') j))" for i
      apply safe
        apply (metis nat.exhaust mwnth_zero mwnth_Suc)
       apply (metis mwnth_zero)
      apply (metis mwnth_Suc)
      done

    have "collapse_reorder_state ?st1 (mwtl \<sigma>') = collapse_reorder_state st \<sigma>'"
      unfolding collapse_reorder_state_def buffer_st1 set_map_default keyset_map_default 1
      apply (subst (3 4) collapse_idx_mwtl)
      unfolding 2 keyset.rep_eq
      by (auto simp: lookup_None_set_conv lookup_Some_set_conv fst_eq_Domain Domain.simps
          split: option.split dest: alist_eq_key_imp_eq)

    show ?thesis sorry (* TODO *)
  qed
  done

lemma reorder_eq_alt: "reorder_state_rel \<sigma> st n \<Longrightarrow> reorder st = sdrop n (reorder_alt \<sigma>)"
  apply (coinduction arbitrary: st \<sigma> n rule: reorder.coinduct)
  subgoal for st \<sigma> n
    apply (induction st rule: reorder.inner_induct)
    subgoal premises ind for st
      apply (cases "fst (reorder_step st)")
      subgoal
        apply (frule ind(1))
         apply (rule reorder_state_rel_step[where xs="[]", simplified, OF ind(2)])
         apply (auto intro: prod_eqI)[]
        apply (subst (1 3) reorder.code)
        apply (simp add: split_beta)
        done
      subgoal for x xs
        apply (insert reorder_state_rel_step[where xs="x # xs" and st'="snd (reorder_step st)", OF ind(2)])
        apply (drule meta_mp)
         apply (auto intro: prod_eqI)[]
        apply (subst (1 3) reorder.code)
        apply (clarsimp simp: split_beta)
        apply (subst stake_sdrop[where n="length xs" and s="sdrop n (stl (reorder_alt \<sigma>))", symmetric])
        apply (erule shift.friend.cong_shift)
        apply (force intro: reorder.cong_base)
        done
      done
    done
  done

lemma reorder'_eq_alt: "reorder' = reorder_alt"
  using reorder_eq_alt[OF reorder_state_rel_init] by (auto simp: reorder'_def fun_eq_iff)


locale wtrace_partition =
  fixes \<sigma> :: "'a itrace" and n :: nat and ps :: "'a wtrace list"
  assumes
    n_greater_0: "n > 0" and
    length_ps_eq_n: "length ps = n" and
    sound_partition: "\<forall>k<n. \<forall>j. \<exists>i. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> w\<Gamma> (ps ! k) j \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>k<n. \<exists>j. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> f \<in> w\<Gamma> (ps ! k) j"

definition wpartition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a wtrace list set" where
  "wpartition n \<sigma> = {ps. wtrace_partition \<sigma> n ps}"

definition least_w\<iota> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "least_w\<iota> \<sigma> i0 = (LEAST i. i0 \<le> i \<and> (\<exists>j. i = w\<iota> \<sigma> j))"

definition w\<iota>_stream :: "'a wtrace \<Rightarrow> nat stream" where
  "w\<iota>_stream \<sigma> = siterate (least_w\<iota> \<sigma> \<circ> Suc) (least_w\<iota> \<sigma> 0)"

definition collapse_w :: "'a wtrace \<Rightarrow> nat \<Rightarrow> 'a set" where
  "collapse_w \<sigma> i = (\<Union>{d. \<exists>j. i = w\<iota> \<sigma> j \<and> d = w\<Gamma> \<sigma> j})"

definition ts_of_w :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "ts_of_w \<sigma> i = w\<tau> \<sigma> (LEAST j. i = w\<iota> \<sigma> j)"

lemma ex_w\<iota>_ge: "\<exists>x\<ge>i. \<exists>j. x = w\<iota> \<sigma> j"
  apply (transfer fixing: i)
  apply (clarsimp simp: wtracep_def)
  apply (drule sincreasing_ex_greater[where j=0 and x=i])
  by (metis gt_ex le_trans less_imp_le_nat smap_alt)

lemma le_least_w\<iota>: "i \<le> least_w\<iota> \<sigma> i"
  unfolding least_w\<iota>_def
  apply (subgoal_tac "i \<le> (LEAST x. i \<le> x \<and> (\<exists>j. x = w\<iota> \<sigma> j)) \<and>
          (\<exists>j. (LEAST x. i \<le> x \<and> (\<exists>j. x = w\<iota> \<sigma> j)) = w\<iota> \<sigma> j)")
   apply (erule conjunct1)
  apply (rule LeastI_ex)
  by (rule ex_w\<iota>_ge)

lemma ssorted_w\<iota>_stream: "ssorted (w\<iota>_stream \<sigma>)"
  by (auto simp: w\<iota>_stream_def intro!: ssorted_siterate order_trans[OF _ le_least_w\<iota>])

lemma sincreasing_w\<iota>_stream: "sincreasing (w\<iota>_stream \<sigma>)"
  by (auto simp: w\<iota>_stream_def intro!: sincreasing_siterate order.strict_trans2[OF _ le_least_w\<iota>])

lemma mono_ts_of_w: "i \<le> j \<Longrightarrow> \<exists>k. i = w\<iota> \<sigma> k \<Longrightarrow> \<exists>k. j = w\<iota> \<sigma> k \<Longrightarrow> ts_of_w \<sigma> i \<le> ts_of_w \<sigma> j"
  unfolding ts_of_w_def
  apply (transfer fixing: i j)
  subgoal for \<sigma>
    apply (clarsimp simp: wtracep_def)
    apply (drule spec2[where P="\<lambda>i j. _ i j \<longrightarrow> ts (_ i) \<le> _ j"])
    apply (erule mp)
    by (metis (mono_tags, lifting) LeastI)
  done

lemma ex_snth_w\<iota>_stream: "\<exists>k. w\<iota>_stream \<sigma> !! i = w\<iota> \<sigma> k"
  apply (induction i)
   apply (auto simp add: w\<iota>_stream_def least_w\<iota>_def simp del: snth.simps intro: LeastI)
  subgoal for i k
    apply (insert LeastI_ex[where P="\<lambda>i. Suc (w\<iota> \<sigma> k) \<le> i \<and> (\<exists>j. i = w\<iota> \<sigma> j)"])
    apply (drule meta_mp)
     apply (rule ex_w\<iota>_ge)
    apply (erule conjunct2)
    done
  done

lemma le_w\<iota>_le_w\<tau>: "w\<iota> \<sigma> i \<le> w\<iota> \<sigma> j \<Longrightarrow> w\<tau> \<sigma> i \<le> w\<tau> \<sigma> j"
  by transfer (simp add: wtracep_def)

lemma w\<tau>_increasing: "\<exists>j>i. w\<tau> \<sigma> i < w\<tau> \<sigma> j"
  by transfer (simp add: wtracep_def sincreasing_def)

lift_definition reorder_w :: "'a wtrace \<Rightarrow> 'a itrace" is
  "\<lambda>\<sigma>. smap (\<lambda>i. \<lparr>db=collapse_w \<sigma> i, ts=ts_of_w \<sigma> i, idx=i\<rparr>) (w\<iota>_stream \<sigma>)"
  apply (simp add: stream.map_comp stream.map_ident ssorted_w\<iota>_stream cong: stream.map_cong)
  subgoal for \<sigma>
    apply safe
    subgoal
      apply (clarsimp simp: sincreasing_def ts_of_w_def)
      subgoal for i
        apply (insert w\<tau>_increasing[of "LEAST j. w\<iota>_stream \<sigma> !! i = w\<iota> \<sigma> j" \<sigma>])
        apply clarify
        subgoal for j
          apply (insert sincreasing_w\<iota>_stream[THEN sincreasing_ex_greater, of "Suc i" "w\<iota> \<sigma> j" \<sigma>])
          apply (clarsimp simp: Suc_le_eq)
          subgoal for k
            apply (rule exI[where x=k])
            apply simp
            apply (subgoal_tac "w\<tau> \<sigma> j \<le> w\<tau> \<sigma> (LEAST j. w\<iota>_stream \<sigma> !! k = w\<iota> \<sigma> j)")
             apply (erule (1) order.strict_trans2)
            apply (rule le_w\<iota>_le_w\<tau>)
            by (metis (mono_tags, lifting) LeastI_ex ex_snth_w\<iota>_stream le_less_linear less_not_sym)
          done
        done
      done
    subgoal for i j
      apply (erule mono_ts_of_w)
       apply (rule ex_snth_w\<iota>_stream)+
      done
    done
  done

lemma wpartition_split: "wpartition n \<le> partition n \<circ>\<then> mapM_set relax_order"
  apply (clarsimp simp: le_fun_def kleisli_set_def partition_def)
  subgoal for \<sigma> ps
    apply (rule exI[where x="map reorder_w ps"])
    apply (auto simp: wpartition_def wtrace_partition_def
        itrace_partition_def in_mapM_set_iff relax_order_def relaxed_order_def)
    sorry (* TODO *)
  done


lemma length_islice[simp]: "length (islice f xs \<sigma>) = length xs"
  by (simp add: islice_def)

lemma in_partition_lengthD: "ps \<in> partition n \<sigma> \<Longrightarrow> length ps = n \<and> n > 0"
  by (simp add: partition_def itrace_partition_def)

lemma foldr_const_max: "foldr (\<lambda>x. max c) xs (a::_::linorder) = (if xs = [] then a else max c a)"
  by (induction xs) simp_all

lemma i\<tau>_islice[simp]: "k < length xs \<Longrightarrow> i\<tau> (islice f xs \<sigma> ! k) j = i\<tau> \<sigma> j"
  by (simp add: islice_def)

lemma i\<iota>_islice[simp]: "k < length xs \<Longrightarrow> i\<iota> (islice f xs \<sigma> ! k) j = i\<iota> \<sigma> j"
  by (simp add: islice_def)

lemma i\<Gamma>_islice[simp]: "k < length xs \<Longrightarrow> i\<Gamma> (islice f xs \<sigma> ! k) j = f (xs ! k) (i\<Gamma> \<sigma> j)"
  by (simp add: islice_def)

lemma partition_islice_transpose:
  "partition n \<circ>\<then> determ (map (islice (\<inter>) xs)) \<circ>\<then> determ transpose \<le>
    islice (\<inter>) xs \<circ>> mapM_set (partition n)"
  apply (clarsimp simp: le_fun_def kleisli_set_def in_mapM_set_iff)
  apply (rule list_all2_all_nthI)
  subgoal 1 for \<sigma> ps
    apply (subgoal_tac "ps \<noteq> []")
     apply (simp add: length_transpose foldr_map foldr_const_max cong: foldr_cong)
    apply (drule in_partition_lengthD)
    apply clarsimp
    done
  subgoal for \<sigma> ps k
    apply (frule 1)
    apply (simp add: nth_transpose cong: map_cong)
    apply (auto simp: partition_def itrace_partition_def cong: conj_cong)
    by (meson le_infI2)
  done

notepad
begin
  fix add_index :: "'a trace \<Rightarrow> 'a itrace"
  fix n :: nat
  fix f :: "'b \<Rightarrow> 'a set"
  fix xs :: "'a set list"

  let ?p = "add_index \<circ>> wpartition n \<circ>\<then> determ (map (wslice (\<inter>) xs)) \<circ>\<then>
    determ transpose \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map reorder')"

  have "?p \<le> add_index \<circ>> partition n \<circ>\<then> mapM_set relax_order \<circ>\<then> determ (map (wslice (\<inter>) xs)) \<circ>\<then>
    determ transpose \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map reorder')"
    unfolding determ_kleisli_set[symmetric]
    by (subst (5) kleisli_set_assoc) (intro kleisli_set_mono order_refl wpartition_split)
  also have "\<dots> \<le> add_index \<circ>> partition n \<circ>\<then> determ (map (islice (\<inter>) xs)) \<circ>\<then> mapM_set (mapM_set relax_order) \<circ>\<then>
    determ transpose \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map reorder')"
  proof -
    have "mapM_set relax_order \<circ>\<then> determ (map (wslice (\<inter>) xs)) \<le> determ (map (islice (\<inter>) xs)) \<circ>\<then> mapM_set (mapM_set relax_order)"
      by (auto simp: mapM_set_determ[symmetric] kleisli_mapM_set determ_kleisli_set
        intro!: mapM_set_mono relax_order_wslice)
    then show ?thesis
      by (subst (1 5) kleisli_set_assoc) (intro kleisli_set_mono order_refl)
  qed
  also have "\<dots> \<le> add_index \<circ>> partition n \<circ>\<then> determ (map (islice (\<inter>) xs)) \<circ>\<then> determ transpose \<circ>\<then>
    mapM_set (mapM_set relax_order) \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map reorder')"
    by (subst (2 6) kleisli_set_assoc) (auto simp: determ_kleisli_set
      intro: kleisli_set_mono mapM_mapM_transpose)
  also have "\<dots> \<le> add_index \<circ>> islice (\<inter>) xs \<circ>> mapM_set (partition n) \<circ>\<then>
    mapM_set (mapM_set relax_order) \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map reorder')"
    unfolding fcomp_assoc unfolding determ_kleisli_set[symmetric]
    apply (subst (1 2) kleisli_set_assoc)
    apply (subst (2) kleisli_set_assoc[symmetric])
    apply (intro kleisli_set_mono order_refl)
    apply (simp add: determ_kleisli_set)
    apply (rule partition_islice_transpose)
    done
end

end
