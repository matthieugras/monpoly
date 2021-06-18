theory Type_Soundness
  imports Typing
begin

interpretation  sat_inst: sat_general "(+)" "(-)" "uminus" "(*)" "(div)" "(mod)" "Event_Data.double_of_event_data" "Event_Data.integer_of_event_data" "(\<le>)"
  by unfold_locales  auto

lemma eval_trm_inst: " sat_inst.eval_trm'  = Formula.eval_trm "
proof -
  have  "sat_inst.eval_trm' v f = Formula.eval_trm v f" for v f
  by (induction f)  auto 
  then show ?thesis  by auto
qed 

lemma eval_agg_op_inst: " sat_inst.eval_agg_op' (\<omega>, d) M  = Formula.eval_agg_op (\<omega>, d) M"
  apply (cases \<omega>)   apply (auto ) apply (induction "flatten_multiset M")  apply (cases \<omega>) apply (auto simp add:  split: list.splits) 
  apply (smt (verit) foldl_cong min_def sat_inst.undef_min_def sat_inst.undef_min_def) 
  by (smt (verit) foldl_cong max_def sat_inst.undef_max_def) 
  

lemma sat_inst_of_sat': "Formula.sat \<sigma> V v i \<phi> = sat_inst.sat' \<sigma> V v i \<phi>"
 apply (induction \<phi> arbitrary: v V i)  apply  (auto simp add: eval_trm_inst less_event_data_def sat_inst.undef_less_def  split: nat.splits)
  using eval_trm_inst apply presburger
                      apply (metis eval_trm_inst) 
  using eval_agg_op_inst apply presburger+  by  (metis match_cong_strong)+


lemma ty_of_sat_safe: "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> 
  Formula.sat \<sigma> V v i \<phi> \<Longrightarrow> x \<in> Formula.fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x) = E x"
  using  sat_inst.sat_general_axioms sat_inst_of_sat'
    sat_general.ty_of_sat'_safe[of  "(+)" "(-)" "uminus" "(*)" "(div)" "(mod)" double_of_event_data integer_of_event_data "(\<le>)"]  
  by auto  blast
 

context sat_general
begin

lemma soundness:
  assumes   "S,E \<turnstile> \<phi>" "\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y" "safe_formula \<phi>"  "wty_envs S \<sigma> V"
   "Formula.nfv \<phi> \<le> length v"
 shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" 

 using assms  proof (induction S E \<phi>  arbitrary: v V i rule: wty_formula.induct)

  case (Pred S p tys E tms )
  from  Pred  have tms_wty: "x \<in> set tms \<Longrightarrow> \<exists>t \<in> set tys. E \<turnstile> x :: t " for x by (metis Pred.hyps(2) in_set_conv_nth list_all2_conv_all_nth)
   have eval_tms_eq: "map (Formula.eval_trm v) tms = map (eval_trm' v) tms" using  tms_wty Pred(3) apply auto
     subgoal for x using eval_trm_sound[of E x _ v] by auto done
  then show ?case apply auto by (metis eval_tms_eq )+
next
  case (Eq E x t y S)
  then show ?case using eval_trm_sound by auto 
next
  case (Less E x1 t x2)
  then show ?case using eval_trm_sound  ty_of_eval_trm value_of_eval_trm[of E x2 v  ] value_of_eval_trm[of E x1 v  ] 
    by (cases t) (auto simp add: undef_less_def undef_less_eq_sound less_event_data_def)
next
  case (LessEq E x1 t x2)
  then show ?case using eval_trm_sound  ty_of_eval_trm value_of_eval_trm[of E x2 v  ] value_of_eval_trm[of E x1 v  ]
    by (cases t) (auto simp add: undef_less_eq_sound) 
next 
  case (Let S E \<phi> p E' \<psi>)
  {
    fix v' i'
    assume assm: " Formula.sat \<sigma> V v' i' \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v' ! y) = E y" sorry
    then have "local.sat' \<sigma> V v' i' \<phi>" using Let.IH[of v' V i'] assm by auto
  }
 moreover{
    fix v' i'
    assume assm: "local.sat' \<sigma> V v' i' \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v' ! y) = E y" sorry
    then have "Formula.sat \<sigma> V v' i' \<phi>" using Let.IH[of v' V i'] assm by auto
  }
  ultimately have "length v' = Formula.nfv \<phi> \<Longrightarrow>  Formula.sat \<sigma> V v' i' \<phi> =  local.sat' \<sigma> V v' i' \<phi>" for v' i' by auto
  from this  have " (\<lambda>a. if a = p then Some (\<lambda>i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>}) else V a) 
  = V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> local.sat' \<sigma> V v i \<phi>})" by fastforce

  then show ?case using Let by auto
next
  case (Agg E y agg_type t tys f S \<phi> d)
  then show ?case  apply auto sorry

next
  case (Neg S E \<phi>)
  from Neg.prems(2) have "safe_formula \<phi>" apply (cases \<phi>) apply auto sorry
  then show ?case sorry

next
  case (And S E \<phi> \<psi>)
  then show ?case sorry
next
  case (Ands \<phi>s S E)
  then show ?case sorry
next
  case (Exists S t E \<phi> )
   {
    fix za
    assume  assm: "Formula.sat \<sigma> V (za # v) i \<phi>" 
    have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,4-5)  nfv assm by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using Exists(3)   by (auto simp add:  fvi_Suc split: nat.splits )

    from this  have "local.sat' \<sigma> V (za # v) i \<phi>" using Exists.IH[of "za#v" V i] Exists(4-5) nfv assm by auto
  }
  moreover {
    fix za
   assume  assm: "local.sat' \<sigma> V (za # v) i \<phi>" 
 have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat'_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,4-5)  nfv assm by auto
    from this have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using Exists(3) assm by (auto simp add: fvi_Suc split: nat.splits )
    from this have " Formula.sat \<sigma> V (za # v) i \<phi>" using Exists.IH[of "za#v" V i] Exists(4-6) nfv_exists[of \<phi> t] assm by auto
  }
  ultimately show ?case   by auto 

next

  case (Since S E \<phi> \<psi> \<I>)
  then show ?case sorry
next
  case (Until S E \<phi> \<psi> \<I>)
  then show ?case sorry
next

  case (MatchF S E x2 x1) 
  from this  have other_IH: "\<phi> \<in> regex.atms x2 \<Longrightarrow> Formula.sat \<sigma> V5 v i5 \<phi> = local.sat' \<sigma> V5 v i5 \<phi>" for \<phi> V5 i5 
    using MatchF apply (auto simp add: regex.pred_set fv_regex_alt) sorry
  then show ?case  using match_cong[OF refl other_IH, where ?r=x2] by auto 
next
  case (MatchP S E x2 x1)
    from this  have other_IH: "\<phi> \<in> regex.atms x2 \<Longrightarrow> Formula.sat \<sigma> V5 v i5 \<phi> = local.sat' \<sigma> V5 v i5 \<phi>" for \<phi> V5 i5 
    apply (auto simp add: regex.pred_set fv_regex_alt) sorry
  then show ?case  using match_cong[OF refl other_IH, where ?r=x2] by auto 
qed  (auto split: nat.splits) 

 (* using assms proof (induction arbitrary: v V i S E rule: safe_formula_induct)

  case (Pred e ts)
  then show ?case sorry
next
  case (Let p \<phi> \<psi>)
  then show ?case sorry
next
  case (And_assign \<phi> \<psi>)
  then show ?case sorry
next
  case (And_safe \<phi> \<psi>)
  then show ?case sorry
next
  case (And_constraint \<phi> \<psi>)
  then show ?case sorry
next
  case (And_Not \<phi> \<psi>)
  then show ?case sorry
next
  case (Ands l pos neg)
  then show ?case sorry

next
  case (Exists \<phi> t)
 {
    fix za
    assume  assm: "Formula.sat \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,5)  nfv assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )

    from this  have "local.sat' \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(5) wty nfv assm by auto
  }
  moreover {
   fix za
    assume  assm: "sat' \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat'_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,5)  nfv assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )

    from this  have "Formula.sat \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(5) wty nfv assm by auto
  }
  ultimately show ?case   by auto 
next
case (Agg y \<omega> tys f \<phi>)
  then show ?case sorry

next
  case (Since \<phi> I \<psi>)
  then show ?case sorry
next
  case (Not_Since \<phi> I \<psi>)
  then show ?case sorry
next
  case (Until \<phi> I \<psi>)
  then show ?case sorry
next
  case (Not_Until \<phi> I \<psi>)
  then show ?case sorry
next
  case (MatchP I r)
  from this  have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V5 v i5 \<phi> = local.sat' \<sigma> V5 v i5 \<phi>" for \<phi> V5 i5 
    using MatchP apply (auto simp add: regex.pred_set fv_regex_alt)  sorry
  then show ?case  using match_cong[OF refl other_IH, where ?r=r] by auto 
next
  case (MatchF I r)
    from this  have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V5 v i5 \<phi> = local.sat' \<sigma> V5 v i5 \<phi>" for \<phi> V5 i5 
    using MatchF apply (auto simp add: regex.pred_set fv_regex_alt) sorry
  then show ?case  using match_cong[OF refl other_IH, where ?r=r] by auto
qed (auto elim: wty_formula.cases split: nat.splits)
*)

end
end