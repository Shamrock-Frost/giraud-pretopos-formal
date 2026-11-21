section \<open>Final reindexings are closed under composition\<close>

theory Final_Reindexing
  imports Diag_Category
begin

text \<open>
  The final reindexings contain the identities and are closed under composition, because a
  composite of final functors is final.
\<close>

subsection \<open>Reading the definition\<close>

text \<open>
  An arrow \<open>w\<close> of \<open>Diag C\<close> is in \<open>W0 C\<close> when its functor part is final, its source diagram agrees
  with the target diagram after the functor part, and each component of its transformation is an
  identity. \<open>W0I\<close> builds a member; the four lemmas after it read each fact back.
\<close>

lemma W0I:
  assumes "w \<in> DArr C" and "final_functor (afun w) (ix (asrc w)) (ix (atgt w))"
    and "agree (ix (asrc w)) (dg (asrc w)) (fcomp (ix (asrc w)) (dg (atgt w)) (afun w))"
    and "\<And>j. j \<in> Ob (ix (asrc w)) \<Longrightarrow> anat w \<cdot> j = id\<^bsub>C\<^esub> (dg (asrc w) \<cdot>\<^sub>o j)"
  shows "w \<in> W0 C"
  unfolding W0_def using assms by (simp add: mem_M)

lemma W0_DArr [simp]: "w \<in> W0 C \<Longrightarrow> w \<in> DArr C"
  unfolding W0_def by simp

lemma W0_final: "w \<in> W0 C \<Longrightarrow> final_functor (afun w) (ix (asrc w)) (ix (atgt w))"
  unfolding W0_def by simp

lemma W0_agree:
  "w \<in> W0 C \<Longrightarrow> agree (ix (asrc w)) (dg (asrc w)) (fcomp (ix (asrc w)) (dg (atgt w)) (afun w))"
  unfolding W0_def by simp

lemma W0_anat [simp]:
  "w \<in> W0 C \<Longrightarrow> j \<in> Ob (ix (asrc w)) \<Longrightarrow> anat w \<cdot> j = id\<^bsub>C\<^esub> (dg (asrc w) \<cdot>\<^sub>o j)"
  unfolding W0_def by (simp add: mem_M)

text \<open>
  The agreement read at an object: the source diagram at \<open>j\<close> is the target diagram at the image
  of \<open>j\<close>.
\<close>

lemma W0_dg_obj:
  assumes "w \<in> W0 C" and "j \<in> Ob (ix (asrc w))"
  shows "dg (atgt w) \<cdot>\<^sub>o (afun w \<cdot>\<^sub>o j) = dg (asrc w) \<cdot>\<^sub>o j"
  using agree_obj[OF W0_agree[OF assms(1)] assms(2)] assms(2) by simp

subsection \<open>Identities\<close>

text \<open>The identity of \<open>X\<close> has functor part \<open>idf\<close>, which is final, and identity components.\<close>

lemma Did_W0:
  assumes C: "category C" and X: "X \<in> DOb C"
  shows "Did C X \<in> W0 C"
proof -
  have "M X"
    using X by (rule DOb_M)
  have cX: "category (ix X)"
    using X by simp
  have ag: "agree (ix X) (dg X) (fcomp (ix X) (dg X) (idf (ix X)))"
    by (rule agreeI) simp_all
  show ?thesis
    by (rule W0I) (use C X \<open>M X\<close> final_idf[OF cX] ag in simp_all)
qed

subsection \<open>Composites\<close>

text \<open>
  For \<open>v : X \<rightarrow> Y\<close> and \<open>w : Y \<rightarrow> Z\<close> in \<open>W0 C\<close>, the composite has functor part \<open>q \<circ> p\<close>, final as a
  composite of final functors between small categories. Its source diagram agrees with
  \<open>dg Z \<circ> (q \<circ> p)\<close> by the two agreements and associativity. Its component at \<open>j\<close> is
  \<open>id \<circ> id\<close> at the one object \<open>dg X j = dg Y (p j)\<close>.
\<close>

lemma Dcomp_W0:
  assumes C: "category C" and v: "v \<in> W0 C" and w: "w \<in> W0 C" and vw: "asrc w = atgt v"
  shows "Dcomp C w v \<in> W0 C"
proof -
  let ?X = "asrc v" and ?Y = "atgt v" and ?Z = "atgt w"
  let ?p = "afun v" and ?q = "afun w"
  have vD: "v \<in> DArr C" and wD: "w \<in> DArr C"
    using v w by simp_all
  have X: "?X \<in> DOb C" and Z: "?Z \<in> DOb C"
    using vD wD by simp_all
  have cX: "category (ix ?X)" and cY: "category (ix ?Y)" and cZ: "category (ix ?Z)"
    using vD wD by simp_all
  have p: "is_functor ?p (ix ?X) (ix ?Y)"
    using vD by (rule DArr_functor)
  have q: "is_functor ?q (ix ?Y) (ix ?Z)"
    using DArr_functor[OF wD] vw by simp
  have pf: "final_functor ?p (ix ?X) (ix ?Y)"
    using v by (rule W0_final)
  have qf: "final_functor ?q (ix ?Y) (ix ?Z)"
    using W0_final[OF w] vw by simp
  have fin: "final_functor (fcomp (ix ?X) ?q ?p) (ix ?X) (ix ?Z)"
    by (rule final_functor_fcomp[OF M_ix M_ix graph_locally_small[OF M_ix] cX cY cZ p q pf qf])
  have agv: "agree (ix ?X) (dg ?X) (fcomp (ix ?X) (dg ?Y) ?p)"
    using v by (rule W0_agree)
  have agw: "agree (ix ?Y) (dg ?Y) (fcomp (ix ?Y) (dg ?Z) ?q)"
    using W0_agree[OF w] vw by simp
  have "agree (ix ?X) (dg ?X) (fcomp (ix ?X) (fcomp (ix ?Y) (dg ?Z) ?q) ?p)"
    using agv fcomp_agree_outer[OF p agw] by (rule agree_trans)
  then have ag: "agree (ix ?X) (dg ?X) (fcomp (ix ?X) (dg ?Z) (fcomp (ix ?X) ?q ?p))"
    by (simp only: fcomp_assoc[OF p])
  have ids: "anat (Dcomp C w v) \<cdot> j = id\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>o j)" if j: "j \<in> Ob (ix ?X)" for j
  proof -
    have pj: "?p \<cdot>\<^sub>o j \<in> Ob (ix (asrc w))"
      using p j vw by simp
    have obj: "dg ?Y \<cdot>\<^sub>o (?p \<cdot>\<^sub>o j) = dg ?X \<cdot>\<^sub>o j"
      using W0_dg_obj[OF v j] .
    have xj: "dg ?X \<cdot>\<^sub>o j \<in> Ob C"
      using DOb_functor[OF X] j by simp
    have "anat (Dcomp C w v) \<cdot> j = anat w \<cdot> (?p \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> anat v \<cdot> j"
      using j by simp
    also have "\<dots> = id\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>o j)"
      using W0_anat[OF w pj] W0_anat[OF v j] obj vw by simp
    also have "\<dots> = id\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>o j)"
      using C xj by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule W0I)
    show "Dcomp C w v \<in> DArr C"
      using C vD wD vw by (rule Dcomp_DArr)
  qed (use fin ag ids in simp_all)
qed

subsection \<open>The theorem\<close>

theorem W0_multiplicative:
  assumes "category C"
  shows "multiplicative (W0 C) (Diag C)"
  unfolding multiplicative_def
proof (intro conjI allI impI)
  fix w
  assume "M w" and "w \<in> W0 C"
  then show "w \<in> Arr (Diag C)"
    by simp
next
  fix X
  assume "M X" and "X \<in> Ob (Diag C)"
  then have X: "X \<in> DOb C"
    by simp
  then show "id\<^bsub>Diag C\<^esub> X \<in> W0 C"
    using Did_W0[OF assms X] by simp
next
  fix v w
  assume "M v" "M w" and v: "v \<in> W0 C" and w: "w \<in> W0 C"
    and vw: "src\<^bsub>Diag C\<^esub> w = tgt\<^bsub>Diag C\<^esub> v"
  have "asrc w = atgt v"
    using vw v w by simp
  then show "w \<circ>\<^bsub>Diag C\<^esub> v \<in> W0 C"
    using Dcomp_W0[OF assms v w] v w by simp
qed

end
