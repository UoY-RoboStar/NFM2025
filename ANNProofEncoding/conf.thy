theory conf
  imports 
    "Z_Toolkit.Channels_Events" "Circus" "Prism_Filter"
begin   


unbundle UTP_Logic_Syntax 


(*DEFINITIONS: *)

definition approx :: "real \<Rightarrow> real \<Rightarrow> real set" where
"approx eps x = {y | y::real. (x-eps) \<le> y \<and> y \<le> (x+eps)}"

definition seq_approx :: "real \<Rightarrow> real list \<Rightarrow> real list set" where
"seq_approx eps xs = {ys | ys. (#ys = #xs) \<and> (\<forall> i \<in> {1..#xs}. 
                     (ys::real list)(i) \<in> (approx (eps) (xs(i)))) }"

definition set_approx :: "real \<Rightarrow> real set \<Rightarrow> (real set) set" where
"set_approx eps xs = {ys | ys. (#ys = #xs) \<and> 
                (\<forall> e \<in> ys. \<exists> e1 \<in> xs.  
                (e \<in> approx eps e1 ))}"

consts process_alpha :: "('e, 's) caction \<Rightarrow> 'e set" ("\<alpha>_") 


definition Approx :: "real \<Rightarrow> ('b \<times> real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction" where
"Approx eps tc P = R3c(\<exists> t. \<exists> a. P\<lbrakk>\<guillemotleft>t\<guillemotright>, ((\<alpha> \<guillemotleft>P\<guillemotright>) - \<guillemotleft>a\<guillemotright>)/tr\<^sup>>, ref\<^sup>>\<rbrakk> \<and>
               (prism_filter_prod \<guillemotleft>tc\<guillemotright> (tr\<^sup>> - tr\<^sup><)) \<in> seq_approx (\<guillemotleft>eps\<guillemotright>) (prism_filter_prod \<guillemotleft>tc\<guillemotright> (\<guillemotleft>t\<guillemotright> - tr\<^sup><)) \<and>
               (prism_filter_prod_set \<guillemotleft>tc\<guillemotright> a) \<in> (set_approx (\<guillemotleft>eps\<guillemotright>) (prism_filter_prod_set \<guillemotleft>tc\<guillemotright> (((\<alpha> \<guillemotleft>P\<guillemotright>) - ($ref\<^sup>>)))))
               )\<^sub>e"

definition conf :: "real \<Rightarrow> ('b \<times> real \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) caction \<Rightarrow> ('e, 's) caction \<Rightarrow> bool" where
"conf eps tc P Q =  (eps \<ge> 0 \<longrightarrow> ((Approx(eps)(tc)(Q) \<sqsubseteq> P)))"

chantype c = inp :: "nat \<times> real" out :: "nat \<times> real"

(*The out set, we take to be the out channel, as that is what we will use in proof.*)
definition Out where "Out = out"

(*Only note is the event type is fixed to c, but is polymorphic in its state type.*)
definition cconf :: "real \<Rightarrow> (c, 's) caction \<Rightarrow> (c, 's) caction \<Rightarrow> bool" where
"cconf eps P Q = (conf eps out P Q)"

lemma list_lem:
  fixes xs :: "'e list" and a :: "'e list" 
  shows "length a = length xs \<and> (\<forall>i\<in>{1..length xs}. a(i) \<in> {xs(i)}) \<longleftrightarrow>
    (a = xs)"                
  apply (simp)
  by (metis One_nat_def Suc_le_eq atLeastAtMost_iff diff_Suc_1 le_eq_less_or_eq less_one not_less_eq nth_equalityI)

(*Trivial Approximation: *)
lemma trivial_approx:"approx 0 x = {x}" unfolding approx_def by auto

(*Value self-approximation: *)
lemma approx_any: "eps \<ge> 0 \<Longrightarrow> x \<in> approx eps x" unfolding approx_def by force

(*Trivial Sequence Approximation:*)
lemma seq_approx0 : "seq_approx 0 xs = {xs}" unfolding seq_approx_def
  using trivial_approx
  apply (auto)
  by (metis One_nat_def list_lem)
  

(*LEMMA 4.2: Sequences Self-Approximation mechanisation. *)
lemma seq_approx_mem : 
  fixes eps::"real"
  assumes "eps \<ge> 0"
  shows "xs \<in> seq_approx eps xs" 
  apply (simp add: seq_approx_def approx_def assms)
  done

(*Modified Lemma 4.2, for set approx.*)
lemma set_approx_mem : 
  fixes eps::"real"
  assumes "eps \<ge> 0"
  shows "xs \<in> set_approx eps xs" 
  unfolding set_approx_def approx_def
  using assms by force


end
