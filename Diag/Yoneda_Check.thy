section \<open>On one-object diagrams, PSh C is C\<close>

theory Yoneda_Check
  imports Colim_Functor
begin

text \<open>
  A check that \<open>PSh C\<close> has the morphisms it should: on one-object diagrams it is \<open>C\<close>. For an
  object \<open>x\<close> of \<open>C\<close>, let \<open>point x\<close> be the diagram of shape the one-arrow category with value
  \<open>x\<close>, standing for the representable presheaf \<open>y x\<close>. Then the arrows \<open>point x \<rightarrow> point y\<close> of
  \<open>PSh C\<close> correspond to the arrows \<open>x \<rightarrow> y\<close> of \<open>C\<close>, by sending \<open>f\<close> to the image of the morphism
  \<open>(id, f)\<close> of diagrams. This is the Yoneda lemma for the model. Nothing here is used by the
  localization theorem.
\<close>

definition one :: cls
  where "one = mkcat (sng \<emptyset>) (sng \<emptyset>) (\<lambda>f\<in>sng \<emptyset>. \<emptyset>) (\<lambda>f\<in>sng \<emptyset>. \<emptyset>) (\<lambda>x\<in>sng \<emptyset>. \<emptyset>) (\<lambda>u\<in>sng \<emptyset> \<times> sng \<emptyset>. \<emptyset>)"

definition point :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "point C x = \<langle>one, mkfun (\<lambda>j\<in>sng \<emptyset>. x) (\<lambda>u\<in>sng \<emptyset>. id\<^bsub>C\<^esub> x)\<rangle>"

definition point_map :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "point_map C f =
    \<langle>\<langle>point C (src\<^bsub>C\<^esub> f), point C (tgt\<^bsub>C\<^esub> f)\<rangle>, \<langle>idf one, \<lambda>j\<in>sng \<emptyset>. f\<rangle>\<rangle>"

subsection \<open>The one-arrow category\<close>

text \<open>
  Its one object and its one arrow are both \<open>\<emptyset>\<close>; every structure map is constantly \<open>\<emptyset>\<close>, also
  off its domain, where application gives \<open>\<emptyset>\<close>.
\<close>

lemma M_one [simp]: "M one"
  by (simp add: one_def)

lemma one_Ob [simp]: "Ob one = sng \<emptyset>"
  by (simp add: one_def)

lemma one_Arr [simp]: "Arr one = sng \<emptyset>"
  by (simp add: one_def)

lemma one_src [simp]: "src\<^bsub>one\<^esub> f = \<emptyset>"
  by (cases "f \<in> sng \<emptyset>") (simp_all add: one_def)

lemma one_tgt [simp]: "tgt\<^bsub>one\<^esub> f = \<emptyset>"
  by (cases "f \<in> sng \<emptyset>") (simp_all add: one_def)

lemma one_id [simp]: "id\<^bsub>one\<^esub> x = \<emptyset>"
  by (cases "x \<in> sng \<emptyset>") (simp_all add: one_def)

lemma one_comp [simp]: "g \<circ>\<^bsub>one\<^esub> f = \<emptyset>"
  by (cases "\<langle>g, f\<rangle> \<in> sng \<emptyset> \<times> sng \<emptyset>") (simp_all add: one_def)

lemma one_category: "category one"
  by (rule categoryI) simp_all

subsection \<open>Point diagrams and their morphisms\<close>

lemma M_point [simp]: "M (point C x)"
  by (simp add: point_def)

lemma ix_point [simp]: "ix (point C x) = one"
  by (simp add: point_def)

lemma dg_point_obj [simp]: "M x \<Longrightarrow> dg (point C x) \<cdot>\<^sub>o \<emptyset> = x"
  by (simp add: point_def)

lemma dg_point_arr [simp]: "dg (point C x) \<cdot>\<^sub>a \<emptyset> = id\<^bsub>C\<^esub> x"
  by (simp add: point_def)

lemma point_functor:
  assumes C: "category C" and x: "x \<in> Ob C"
  shows "is_functor (dg (point C x)) one C"
  by (rule is_functorI) (use C x in \<open>simp_all add: mem_M\<close>)

lemma point_DOb [simp]:
  assumes "category C" and "x \<in> Ob C"
  shows "point C x \<in> DOb C"
proof -
  have "point C x = \<langle>one, dg (point C x)\<rangle>"
    by (simp add: point_def)
  moreover have "\<langle>one, dg (point C x)\<rangle> \<in> DOb C"
    using one_category point_functor[OF assms] by simp
  ultimately show ?thesis
    by simp
qed

lemma asrc_point_map [simp]: "asrc (point_map C f) = point C (src\<^bsub>C\<^esub> f)"
  by (simp add: point_map_def)

lemma atgt_point_map [simp]: "atgt (point_map C f) = point C (tgt\<^bsub>C\<^esub> f)"
  by (simp add: point_map_def)

lemma afun_point_map [simp]: "afun (point_map C f) = idf one"
  by (simp add: point_map_def)

lemma anat_point_map_app [simp]: "M f \<Longrightarrow> anat (point_map C f) \<cdot> \<emptyset> = f"
  by (simp add: point_map_def)

lemma point_map_DArr:
  assumes C: "category C" and f: "f \<in> Arr C"
  shows "point_map C f \<in> DArr C"
  unfolding point_map_def
proof (rule DArrI)
  show "point C (src\<^bsub>C\<^esub> f) \<in> DOb C" and "point C (tgt\<^bsub>C\<^esub> f) \<in> DOb C"
    using C f by simp_all
  show "strict_functor (idf one) (ix (point C (src\<^bsub>C\<^esub> f))) (ix (point C (tgt\<^bsub>C\<^esub> f)))"
    using idf_strict[OF one_category] by simp
  show "(\<lambda>j\<in>sng \<emptyset>. f) = (\<lambda>j\<in>Ob (ix (point C (src\<^bsub>C\<^esub> f))). (\<lambda>j\<in>sng \<emptyset>. f) \<cdot> j)"
  proof -
    have "(\<lambda>j\<in>sng \<emptyset>. f) = (\<lambda>j\<in>sng \<emptyset>. (\<lambda>j\<in>sng \<emptyset>. f) \<cdot> j)"
      by (rule Lam_eqI) (use f in \<open>simp add: mem_M\<close>)
    then show ?thesis
      by (simp only: ix_point one_Ob)
  qed
qed (use C f in \<open>simp_all add: mem_M\<close>)

lemma colim_point_map_PArr:
  assumes "category C" and "locally_small C" and "f \<in> Arr C"
  shows "colim_functor C \<cdot>\<^sub>a point_map C f \<in> PArr C"
  using assms point_map_DArr[OF assms(1,3)] by simp

lemma colim_point_map_body:
  assumes "category C" and "locally_small C" and f: "f \<in> Arr C"
  shows "body (colim_functor C \<cdot>\<^sub>a point_map C f) \<cdot> \<emptyset> =
    cc (cgraph C (point C (tgt\<^bsub>C\<^esub> f)) (src\<^bsub>C\<^esub> f)) \<langle>\<emptyset>, f\<rangle>"
  using assms point_map_DArr[OF assms(1,3)] by (simp add: mem_M)

subsection \<open>The comma graph over a point has only loops\<close>

text \<open>
  An edge of \<open>(z \<down> point y)\<close> goes from \<open>\<langle>\<emptyset>, g\<rangle>\<close> to \<open>\<langle>\<emptyset>, id \<circ> g\<rangle> = \<langle>\<emptyset>, g\<rangle>\<close>, so every singleton is
  closed and connected vertices are equal.
\<close>

lemma point_conn:
  assumes C: "category C" and y: "y \<in> Ob C" and u: "M u"
    and c: "conn (cgraph C (point C y) z) u v"
  shows "v = u"
proof -
  have ecl: "eclosed (cgraph C (point C y) z) (sng u)"
  proof (rule eclosedI)
    fix a b
    assume "M a" and "M b" and e: "\<langle>a, b\<rangle> \<in> cgraph C (point C y) z"
    obtain g e' where a: "a = \<langle>src\<^bsub>ix (point C y)\<^esub> e', g\<rangle>"
      and b: "b = \<langle>tgt\<^bsub>ix (point C y)\<^esub> e', dg (point C y) \<cdot>\<^sub>a e' \<circ>\<^bsub>C\<^esub> g\<rangle>"
      and e': "e' \<in> Arr (ix (point C y))" and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = z"
      "tgt\<^bsub>C\<^esub> g = dg (point C y) \<cdot>\<^sub>o src\<^bsub>ix (point C y)\<^esub> e'"
      using e \<open>M a\<close> \<open>M b\<close> by (rule comma_edge_pairE)
    have "e' = \<emptyset>"
      using e' by simp
    then have "a = b"
      using a b g C y by (simp add: mem_M)
    then show "a \<in> sng u \<longleftrightarrow> b \<in> sng u"
      by simp
  qed
  have "v \<in> sng u"
    by (rule connD[OF c M_sng ecl]) (simp add: u)
  then show ?thesis
    by simp
qed

subsection \<open>The theorem\<close>

text \<open>
  An arrow \<open>\<phi> : point x \<rightarrow> point y\<close> has at \<open>\<emptyset>\<close> a component of \<open>(x \<down> point y)\<close>, which is a singleton
  \<open>{\<langle>\<emptyset>, f\<rangle>}\<close>; then \<open>\<phi>\<close> is the image of \<open>(id, f)\<close>, and \<open>f\<close> is determined by \<open>\<phi>\<close>.
\<close>

lemma colim_point_map_eqI:
  assumes C: "category C" and ls: "locally_small C" and f: "f \<in> Hom C x y"
    and \<phi>: "\<phi> \<in> PArr C" and \<phi>s: "asrc \<phi> = point C x" and \<phi>t: "atgt \<phi> = point C y"
    and mem: "\<langle>\<emptyset>, f\<rangle> \<in> body \<phi> \<cdot> \<emptyset>"
  shows "colim_functor C \<cdot>\<^sub>a point_map C f = \<phi>"
proof -
  have fA: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = y"
    using f by simp_all
  let ?\<psi> = "colim_functor C \<cdot>\<^sub>a point_map C f"
  have \<psi>: "?\<psi> \<in> PArr C"
    by (rule colim_point_map_PArr[OF C ls fA(1)])
  have DA: "point_map C f \<in> DArr C"
    by (rule point_map_DArr[OF C fA(1)])
  show ?thesis
  proof (rule PArr_eqI[OF \<psi> \<phi>])
    show "asrc ?\<psi> = asrc \<phi>" and "atgt ?\<psi> = atgt \<phi>"
      using DA fA \<phi>s \<phi>t by simp_all
    fix j
    assume "j \<in> Ob (ix (asrc ?\<psi>))"
    then have j: "j = \<emptyset>"
      using DA by simp
    have j0: "\<emptyset> \<in> Ob (ix (asrc ?\<psi>))" and j1: "\<emptyset> \<in> Ob (ix (asrc \<phi>))"
      using DA \<phi>s by simp_all
    have mem\<psi>: "\<langle>\<emptyset>, f\<rangle> \<in> body ?\<psi> \<cdot> \<emptyset>"
      using colim_point_map_body[OF C ls fA(1)] by (simp add: mem_M[OF fA(1)])
    have "body ?\<psi> \<cdot> \<emptyset> = cc (cgraph C (atgt ?\<psi>) (dg (asrc ?\<psi>) \<cdot>\<^sub>o \<emptyset>)) \<langle>\<emptyset>, f\<rangle>"
      by (rule PArr_body_eq_cc[OF C ls \<psi> j0 mem\<psi>])
    also have "\<dots> = cc (cgraph C (atgt \<phi>) (dg (asrc \<phi>) \<cdot>\<^sub>o \<emptyset>)) \<langle>\<emptyset>, f\<rangle>"
      using DA fA \<phi>s \<phi>t by simp
    also have "\<dots> = body \<phi> \<cdot> \<emptyset>"
      by (rule PArr_body_eq_cc[OF C ls \<phi> j1 mem, symmetric])
    finally show "body ?\<psi> \<cdot> j = body \<phi> \<cdot> j"
      unfolding j .
  qed
qed

theorem yoneda_check:
  assumes "category C" and "locally_small C" and "x \<in> Ob C" and "y \<in> Ob C"
  shows "point C x \<in> Ob (PSh C)"
    and "\<forall>\<^sub>s f. f \<in> Hom C x y \<longrightarrow>
      colim_functor C \<cdot>\<^sub>a point_map C f \<in> Hom (PSh C) (point C x) (point C y)"
    and "\<forall>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) (point C x) (point C y) \<longrightarrow>
      (\<exists>\<^sub>s f. f \<in> Hom C x y \<and> colim_functor C \<cdot>\<^sub>a point_map C f = \<phi> \<and>
        (\<forall>\<^sub>s f'. f' \<in> Hom C x y \<longrightarrow> colim_functor C \<cdot>\<^sub>a point_map C f' = \<phi> \<longrightarrow> f' = f))"
proof -
  note C = assms(1) and ls = assms(2) and x = assms(3) and y = assms(4)
  show "point C x \<in> Ob (PSh C)"
    using C x by simp
  show "\<forall>\<^sub>s f. f \<in> Hom C x y \<longrightarrow>
      colim_functor C \<cdot>\<^sub>a point_map C f \<in> Hom (PSh C) (point C x) (point C y)"
  proof (intro allI impI)
    fix f
    assume "M f" and "f \<in> Hom C x y"
    then have fA: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = y"
      by simp_all
    have DA: "point_map C f \<in> DArr C"
      by (rule point_map_DArr[OF C fA(1)])
    have "colim_functor C \<cdot>\<^sub>a point_map C f \<in> PArr C"
      by (rule colim_point_map_PArr[OF C ls fA(1)])
    then show "colim_functor C \<cdot>\<^sub>a point_map C f \<in> Hom (PSh C) (point C x) (point C y)"
      using DA fA by simp
  qed
  show "\<forall>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) (point C x) (point C y) \<longrightarrow>
      (\<exists>\<^sub>s f. f \<in> Hom C x y \<and> colim_functor C \<cdot>\<^sub>a point_map C f = \<phi> \<and>
        (\<forall>\<^sub>s f'. f' \<in> Hom C x y \<longrightarrow> colim_functor C \<cdot>\<^sub>a point_map C f' = \<phi> \<longrightarrow> f' = f))"
  proof (intro allI impI)
    fix \<phi>
    assume "M \<phi>" and \<phi>H: "\<phi> \<in> Hom (PSh C) (point C x) (point C y)"
    have \<phi>: "\<phi> \<in> PArr C"
      using \<phi>H by simp
    have \<phi>s: "asrc \<phi> = point C x" and \<phi>t: "atgt \<phi> = point C y"
      using \<phi> \<phi>H by simp_all
    have j0: "\<emptyset> \<in> Ob (ix (asrc \<phi>))"
      using \<phi>s by simp
    obtain k g where kg: "\<langle>k, g\<rangle> \<in> body \<phi> \<cdot> \<emptyset>" and "M k" and "M g"
      and k: "k \<in> Ob (ix (atgt \<phi>))" and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = dg (asrc \<phi>) \<cdot>\<^sub>o \<emptyset>"
      "tgt\<^bsub>C\<^esub> g = dg (atgt \<phi>) \<cdot>\<^sub>o k"
      using \<phi> j0 by (rule PArr_body_ex)
    have k0: "k = \<emptyset>"
      using k \<phi>t by simp
    have gH: "g \<in> Hom C x y"
      using g k0 \<phi>s \<phi>t x y by (simp add: mem_M)
    have mem: "\<langle>\<emptyset>, g\<rangle> \<in> body \<phi> \<cdot> \<emptyset>"
      using kg k0 by simp
    have eq: "colim_functor C \<cdot>\<^sub>a point_map C g = \<phi>"
      by (rule colim_point_map_eqI[OF C ls gH \<phi> \<phi>s \<phi>t mem])
    have uniq: "f' = g" if f': "f' \<in> Hom C x y" and eq': "colim_functor C \<cdot>\<^sub>a point_map C f' = \<phi>"
      for f'
    proof -
      have f'A: "f' \<in> Arr C" "src\<^bsub>C\<^esub> f' = x" "tgt\<^bsub>C\<^esub> f' = y"
        using f' by simp_all
      have "\<langle>\<emptyset>, f'\<rangle> \<in> body (colim_functor C \<cdot>\<^sub>a point_map C f') \<cdot> \<emptyset>"
        using colim_point_map_body[OF C ls f'A(1)] by (simp add: mem_M[OF f'A(1)])
      then have mem': "\<langle>\<emptyset>, f'\<rangle> \<in> body \<phi> \<cdot> \<emptyset>"
        unfolding eq' .
      have "conn (cgraph C (atgt \<phi>) (dg (asrc \<phi>) \<cdot>\<^sub>o \<emptyset>)) \<langle>\<emptyset>, g\<rangle> \<langle>\<emptyset>, f'\<rangle>"
        by (rule PArr_body_conn[OF C ls \<phi> j0 mem mem'])
      then have "conn (cgraph C (point C y) (dg (asrc \<phi>) \<cdot>\<^sub>o \<emptyset>)) \<langle>\<emptyset>, g\<rangle> \<langle>\<emptyset>, f'\<rangle>"
        unfolding \<phi>t .
      then have "\<langle>\<emptyset>, f'\<rangle> = \<langle>\<emptyset>, g\<rangle>"
        by (rule point_conn[OF C y M_opair])
      then show "f' = g"
        using mem_M[OF f'A(1)] mem_M[OF g(1)] by simp
    qed
    show "\<exists>\<^sub>s f. f \<in> Hom C x y \<and> colim_functor C \<cdot>\<^sub>a point_map C f = \<phi> \<and>
        (\<forall>\<^sub>s f'. f' \<in> Hom C x y \<longrightarrow> colim_functor C \<cdot>\<^sub>a point_map C f' = \<phi> \<longrightarrow> f' = f)"
      using gH eq uniq mem_M[OF g(1)] by blast
  qed
qed

end
