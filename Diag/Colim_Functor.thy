section \<open>The colimit functor\<close>

theory Colim_Functor
  imports PSh_Category
begin

text \<open>
  \<open>colim_functor C\<close> preserves identities: the identity \<open>(idf, id)\<close> of \<open>X\<close> goes to the family of
  the components of the \<open>\<langle>j, id\<rangle>\<close>, which is \<open>Pid C X\<close>. It preserves composites: at \<open>j\<close>, the
  composite of the images of \<open>(p, \<alpha>)\<close> and \<open>(q, \<beta>)\<close> is computed by the key lemma from the
  representatives \<open>\<langle>p \<cdot>\<^sub>o j, \<alpha> \<cdot> j\<rangle>\<close> and \<open>\<langle>q \<cdot>\<^sub>o (p \<cdot>\<^sub>o j), \<beta> \<cdot> (p \<cdot>\<^sub>o j)\<rangle>\<close>, which gives the component of
  \<open>\<langle>q \<cdot>\<^sub>o (p \<cdot>\<^sub>o j), \<beta> \<cdot> (p \<cdot>\<^sub>o j) \<circ> \<alpha> \<cdot> j\<rangle>\<close>, the value of the image of \<open>(q p, \<beta> p \<circ> \<alpha>)\<close>.
\<close>

lemma colim_functor_id:
  assumes C: "category C" and ls: "locally_small C" and X: "X \<in> DOb C"
  shows "colim_functor C \<cdot>\<^sub>a Did C X = Pid C X"
proof (rule PArr_eqI)
  show "colim_functor C \<cdot>\<^sub>a Did C X \<in> PArr C" and "Pid C X \<in> PArr C"
    using C ls X by simp_all
  show "asrc (colim_functor C \<cdot>\<^sub>a Did C X) = asrc (Pid C X)"
    and "atgt (colim_functor C \<cdot>\<^sub>a Did C X) = atgt (Pid C X)"
    using C X by (simp_all add: mem_M)
  fix j
  assume "j \<in> Ob (ix (asrc (colim_functor C \<cdot>\<^sub>a Did C X)))"
  then have j: "j \<in> Ob (ix X)"
    using C X by (simp add: mem_M)
  show "body (colim_functor C \<cdot>\<^sub>a Did C X) \<cdot> j = body (Pid C X) \<cdot> j"
    using C ls X j by (simp add: mem_M)
qed

lemma colim_functor_comp:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> DArr C" and b: "b \<in> DArr C"
    and ab: "asrc b = atgt a"
  shows "colim_functor C \<cdot>\<^sub>a Dcomp C b a =
    Pcomp C (colim_functor C \<cdot>\<^sub>a b) (colim_functor C \<cdot>\<^sub>a a)"
proof -
  let ?A = "colim_functor C \<cdot>\<^sub>a a" and ?B = "colim_functor C \<cdot>\<^sub>a b"
  have ba: "Dcomp C b a \<in> DArr C"
    by (rule Dcomp_DArr[OF C a b ab])
  have A: "?A \<in> PArr C" and B: "?B \<in> PArr C"
    using C ls a b by simp_all
  have AB: "asrc ?B = atgt ?A"
    using a b ab by simp
  show ?thesis
  proof (rule PArr_eqI[OF colim_functor_PArr[OF C ls ba] Pcomp_PArr[OF C ls A B AB]])
    show "asrc (colim_functor C \<cdot>\<^sub>a Dcomp C b a) = asrc (Pcomp C ?B ?A)"
      using a ba by simp
    show "atgt (colim_functor C \<cdot>\<^sub>a Dcomp C b a) = atgt (Pcomp C ?B ?A)"
      using b ba by simp
    fix j
    assume "j \<in> Ob (ix (asrc (colim_functor C \<cdot>\<^sub>a Dcomp C b a)))"
    then have j: "j \<in> Ob (ix (asrc a))"
      using ba by simp
    let ?p = "afun a" and ?\<alpha> = "anat a" and ?q = "afun b" and ?\<beta> = "anat b"
    have p: "is_functor ?p (ix (asrc a)) (ix (atgt a))"
      by (rule DArr_functor[OF a])
    have pj: "?p \<cdot>\<^sub>o j \<in> Ob (ix (asrc b))"
      using p j ab by simp
    have jA: "j \<in> Ob (ix (asrc ?A))"
      using a j by simp
    have v1: "\<langle>?p \<cdot>\<^sub>o j, ?\<alpha> \<cdot> j\<rangle> \<in> body ?A \<cdot> j"
      using C ls a j by simp
    have v2: "\<langle>?q \<cdot>\<^sub>o (?p \<cdot>\<^sub>o j), ?\<beta> \<cdot> (?p \<cdot>\<^sub>o j)\<rangle> \<in> body ?B \<cdot> (?p \<cdot>\<^sub>o j)"
      using C ls b pj by simp
    have "body (Pcomp C ?B ?A) \<cdot> j =
        cc (cgraph C (atgt ?B) (dg (asrc ?A) \<cdot>\<^sub>o j))
          \<langle>?q \<cdot>\<^sub>o (?p \<cdot>\<^sub>o j), ?\<beta> \<cdot> (?p \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> j\<rangle>"
      by (rule Pcomp_body_eq[OF C ls A B AB jA v1 v2 M_obj M_app M_obj M_app])
    then show "body (colim_functor C \<cdot>\<^sub>a Dcomp C b a) \<cdot> j = body (Pcomp C ?B ?A) \<cdot> j"
      using C ls ba a b j by simp
  qed
qed

theorem colim_functor:
  assumes "category C" and "locally_small C"
  shows "is_functor (colim_functor C) (Diag C) (PSh C)"
    and "identity_on_objects (colim_functor C) (Diag C) (PSh C)"
proof -
  show "is_functor (colim_functor C) (Diag C) (PSh C)"
    by (rule is_functorI) (use assms in \<open>simp_all add: colim_functor_id colim_functor_comp\<close>)
  show "identity_on_objects (colim_functor C) (Diag C) (PSh C)"
    unfolding identity_on_objects_def by simp
qed

end
