section \<open>Reading the presheaf model\<close>

theory PSh_Basics
  imports Diag_Category
begin

text \<open>
  What an arrow of \<open>PSh C\<close> is, read off from the definitions: rules to build one and to take one
  apart, what being a connected component gives, the six components of \<open>PSh C\<close>, the parts of
  \<open>Pid\<close> and \<open>Pcomp\<close>, and how \<open>colim_functor C\<close> acts. Whatever needs a component to be a set
  asks for \<open>category C\<close> and \<open>locally_small C\<close>.
\<close>

subsection \<open>Objects and their comma graphs\<close>

text \<open>
  The diagram of an object, applied to objects and arrows of its index category; these are the
  rules of \<open>functor_obj\<close> and friends for the functor \<open>DOb_functor\<close>, stated so that the
  simplifier can use them. Over an object \<open>Y\<close> of \<open>DOb C\<close> the comma graph \<open>(x \<down> dg Y)\<close> is small,
  so its components are sets, and the component of a vertex consists of vertices.
\<close>

lemma DOb_dg_obj [simp]: "X \<in> DOb C \<Longrightarrow> j \<in> Ob (ix X) \<Longrightarrow> dg X \<cdot>\<^sub>o j \<in> Ob C"
  by (rule functor_obj[OF DOb_functor])

lemma DOb_dg_arr [simp]: "X \<in> DOb C \<Longrightarrow> u \<in> Arr (ix X) \<Longrightarrow> dg X \<cdot>\<^sub>a u \<in> Arr C"
  by (rule functor_arr[OF DOb_functor])

lemma DOb_dg_src [simp]: "X \<in> DOb C \<Longrightarrow> u \<in> Arr (ix X) \<Longrightarrow> src\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>a u) = dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> u"
  by (rule functor_src[OF DOb_functor])

lemma DOb_dg_tgt [simp]: "X \<in> DOb C \<Longrightarrow> u \<in> Arr (ix X) \<Longrightarrow> tgt\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>a u) = dg X \<cdot>\<^sub>o tgt\<^bsub>ix X\<^esub> u"
  by (rule functor_tgt[OF DOb_functor])

lemma M_cverts [simp]:
  "locally_small C \<Longrightarrow> Y \<in> DOb C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> M (cverts C Y x)"
  by (rule M_comma_verts[OF M_ix _ _ DOb_functor])

lemma M_cgraph [simp]:
  "category C \<Longrightarrow> locally_small C \<Longrightarrow> Y \<in> DOb C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> M (cgraph C Y x)"
  by (rule M_comma_edges[OF M_ix _ _ DOb_category _ DOb_functor])

lemma M_cgraph_cc [simp]:
  "category C \<Longrightarrow> locally_small C \<Longrightarrow> Y \<in> DOb C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> M v \<Longrightarrow> M (cc (cgraph C Y x) v)"
  by (rule M_cc[OF M_cgraph])

lemma cgraph_conn_verts:
  "category C \<Longrightarrow> locally_small C \<Longrightarrow> Y \<in> DOb C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> v \<in> cverts C Y x \<Longrightarrow>
    conn (cgraph C Y x) v w \<Longrightarrow> w \<in> cverts C Y x"
  by (rule comma_conn_verts[OF M_ix _ _ DOb_category _ DOb_functor])

subsection \<open>Arrows\<close>

text \<open>
  An arrow \<open>\<langle>\<langle>X, Y\<rangle>, \<phi>\<rangle>\<close>: a family \<open>\<phi>\<close>, equal to its own \<open>\<lambda>\<close> over the objects of \<open>ix X\<close>, of
  components of the comma graphs \<open>(dg X \<cdot>\<^sub>o j \<down> dg Y)\<close>, compatible with the arrows of \<open>ix X\<close>.
  \<open>PArrI\<close> builds one from a family that is its own \<open>\<lambda>\<close>; \<open>PArr_LamI\<close> from a \<open>\<lambda>\<close>-term, which is how
  \<open>Pid\<close>, \<open>Pcomp\<close> and \<open>colim_functor\<close> are written. \<open>PArrD\<close> reads every property back through
  the projections, and the lemmas after it name each part.
\<close>

lemma PArrI:
  assumes X: "X \<in> DOb C" and Y: "Y \<in> DOb C" and \<phi>: "\<phi> = (\<lambda>j\<in>Ob (ix X). \<phi> \<cdot> j)"
    and comp: "\<And>j. j \<in> Ob (ix X) \<Longrightarrow>
      \<exists>\<^sub>s v. v \<in> cverts C Y (dg X \<cdot>\<^sub>o j) \<and> \<phi> \<cdot> j = cc (cgraph C Y (dg X \<cdot>\<^sub>o j)) v"
    and compat: "\<And>u k f. u \<in> Arr (ix X) \<Longrightarrow> M k \<Longrightarrow> M f \<Longrightarrow> \<langle>k, f\<rangle> \<in> \<phi> \<cdot> tgt\<^bsub>ix X\<^esub> u \<Longrightarrow>
      \<langle>k, f \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u\<rangle> \<in> \<phi> \<cdot> src\<^bsub>ix X\<^esub> u"
  shows "\<langle>\<langle>X, Y\<rangle>, \<phi>\<rangle> \<in> PArr C"
proof -
  have "M X" and "M Y"
    using X Y by (simp_all add: mem_M)
  have "M (\<lambda>j\<in>Ob (ix X). \<phi> \<cdot> j)"
    by simp
  then have "M \<phi>"
    by (metis \<phi>)
  show ?thesis
    unfolding PArr_def
    apply (rule CollI)
      apply dfn
     apply simp
    using X Y \<phi> comp compat \<open>M X\<close> \<open>M Y\<close> \<open>M \<phi>\<close> by blast
qed

lemma PArr_LamI:
  assumes C: "category C" and ls: "locally_small C" and X: "X \<in> DOb C" and Y: "Y \<in> DOb C"
    and t: "dcls t"
    and comp: "\<And>j. j \<in> Ob (ix X) \<Longrightarrow>
      \<exists>\<^sub>s v. v \<in> cverts C Y (dg X \<cdot>\<^sub>o j) \<and> t j = cc (cgraph C Y (dg X \<cdot>\<^sub>o j)) v"
    and compat: "\<And>u k f. u \<in> Arr (ix X) \<Longrightarrow> M k \<Longrightarrow> M f \<Longrightarrow> \<langle>k, f\<rangle> \<in> t (tgt\<^bsub>ix X\<^esub> u) \<Longrightarrow>
      \<langle>k, f \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u\<rangle> \<in> t (src\<^bsub>ix X\<^esub> u)"
  shows "\<langle>\<langle>X, Y\<rangle>, \<lambda>j\<in>Ob (ix X). t j\<rangle> \<in> PArr C"
proof -
  have Mt: "M (t j)" if j: "j \<in> Ob (ix X)" for j
  proof -
    obtain v where "M v" and v: "t j = cc (cgraph C Y (dg X \<cdot>\<^sub>o j)) v"
      using comp[OF j] by blast
    have "dg X \<cdot>\<^sub>o j \<in> Ob C"
      using X j by simp
    then show ?thesis
      unfolding v using C ls Y \<open>M v\<close> by simp
  qed
  have app: "(\<lambda>j\<in>Ob (ix X). t j) \<cdot> j = t j" if j: "j \<in> Ob (ix X)" for j
    by (rule app_Lam[OF t j Mt[OF j]])
  have cX: "category (ix X)"
    using X by simp
  show ?thesis
  proof (rule PArrI[OF X Y])
    show "(\<lambda>j\<in>Ob (ix X). t j) = (\<lambda>j\<in>Ob (ix X). (\<lambda>j\<in>Ob (ix X). t j) \<cdot> j)"
      by (rule Lam_eqI) (rule app[symmetric])
    show "\<exists>\<^sub>s v. v \<in> cverts C Y (dg X \<cdot>\<^sub>o j) \<and>
        (\<lambda>j\<in>Ob (ix X). t j) \<cdot> j = cc (cgraph C Y (dg X \<cdot>\<^sub>o j)) v"
      if j: "j \<in> Ob (ix X)" for j
      unfolding app[OF j] by (rule comp[OF j])
    show "\<langle>k, f \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u\<rangle> \<in> (\<lambda>j\<in>Ob (ix X). t j) \<cdot> src\<^bsub>ix X\<^esub> u"
      if u: "u \<in> Arr (ix X)" and "M k" and "M f"
        and kf: "\<langle>k, f\<rangle> \<in> (\<lambda>j\<in>Ob (ix X). t j) \<cdot> tgt\<^bsub>ix X\<^esub> u" for u k f
    proof -
      have st: "src\<^bsub>ix X\<^esub> u \<in> Ob (ix X)" "tgt\<^bsub>ix X\<^esub> u \<in> Ob (ix X)"
        using cX u by simp_all
      have "\<langle>k, f\<rangle> \<in> t (tgt\<^bsub>ix X\<^esub> u)"
        using kf unfolding app[OF st(2)] .
      then have "\<langle>k, f \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u\<rangle> \<in> t (src\<^bsub>ix X\<^esub> u)"
        by (rule compat[OF u \<open>M k\<close> \<open>M f\<close>])
      then show ?thesis
        unfolding app[OF st(1)] .
    qed
  qed
qed

lemma PArr_unfold:
  assumes "a \<in> PArr C"
  shows "\<exists>\<^sub>s X Y \<phi>. a = \<langle>\<langle>X, Y\<rangle>, \<phi>\<rangle> \<and> X \<in> DOb C \<and> Y \<in> DOb C \<and>
      \<phi> = (\<lambda>j\<in>Ob (ix X). \<phi> \<cdot> j) \<and>
      (\<forall>\<^sub>s j. j \<in> Ob (ix X) \<longrightarrow>
        (\<exists>\<^sub>s v. v \<in> cverts C Y (dg X \<cdot>\<^sub>o j) \<and> \<phi> \<cdot> j = cc (cgraph C Y (dg X \<cdot>\<^sub>o j)) v)) \<and>
      (\<forall>\<^sub>s u k f. u \<in> Arr (ix X) \<longrightarrow> \<langle>k, f\<rangle> \<in> \<phi> \<cdot> tgt\<^bsub>ix X\<^esub> u \<longrightarrow>
        \<langle>k, f \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u\<rangle> \<in> \<phi> \<cdot> src\<^bsub>ix X\<^esub> u)"
  using assms unfolding PArr_def by (rule CollD) dfn

lemma PArrD:
  assumes "a \<in> PArr C"
  shows "a = \<langle>\<langle>asrc a, atgt a\<rangle>, body a\<rangle>"
    and "asrc a \<in> DOb C"
    and "atgt a \<in> DOb C"
    and "body a = (\<lambda>j\<in>Ob (ix (asrc a)). body a \<cdot> j)"
    and "\<And>j. j \<in> Ob (ix (asrc a)) \<Longrightarrow>
      \<exists>\<^sub>s v. v \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j) \<and>
        body a \<cdot> j = cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v"
    and "\<And>u k f. u \<in> Arr (ix (asrc a)) \<Longrightarrow> M k \<Longrightarrow> M f \<Longrightarrow> \<langle>k, f\<rangle> \<in> body a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u \<Longrightarrow>
      \<langle>k, f \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u\<rangle> \<in> body a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u"
proof -
  obtain X Y \<phi> where "M X" and "M Y" and "M \<phi>" and a: "a = \<langle>\<langle>X, Y\<rangle>, \<phi>\<rangle>"
    and X: "X \<in> DOb C" and Y: "Y \<in> DOb C" and \<phi>: "\<phi> = (\<lambda>j\<in>Ob (ix X). \<phi> \<cdot> j)"
    and comp: "\<forall>\<^sub>s j. j \<in> Ob (ix X) \<longrightarrow>
      (\<exists>\<^sub>s v. v \<in> cverts C Y (dg X \<cdot>\<^sub>o j) \<and> \<phi> \<cdot> j = cc (cgraph C Y (dg X \<cdot>\<^sub>o j)) v)"
    and compat: "\<forall>\<^sub>s u k f. u \<in> Arr (ix X) \<longrightarrow> \<langle>k, f\<rangle> \<in> \<phi> \<cdot> tgt\<^bsub>ix X\<^esub> u \<longrightarrow>
      \<langle>k, f \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u\<rangle> \<in> \<phi> \<cdot> src\<^bsub>ix X\<^esub> u"
    using PArr_unfold[OF assms] by blast
  have proj: "asrc a = X" "atgt a = Y" "body a = \<phi>"
    using \<open>M X\<close> \<open>M Y\<close> \<open>M \<phi>\<close> by (simp_all add: a)
  show "a = \<langle>\<langle>asrc a, atgt a\<rangle>, body a\<rangle>"
    unfolding proj by (fact a)
  show "asrc a \<in> DOb C"
    unfolding proj by (fact X)
  show "atgt a \<in> DOb C"
    unfolding proj by (fact Y)
  show "body a = (\<lambda>j\<in>Ob (ix (asrc a)). body a \<cdot> j)"
    unfolding proj by (fact \<phi>)
  show "\<exists>\<^sub>s v. v \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j) \<and>
      body a \<cdot> j = cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v"
    if "j \<in> Ob (ix (asrc a))" for j
    using comp that mem_M unfolding proj by blast
  show "\<langle>k, f \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u\<rangle> \<in> body a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u"
    if "u \<in> Arr (ix (asrc a))" and "M k" and "M f" and "\<langle>k, f\<rangle> \<in> body a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u"
    for u k f
    using compat that mem_M unfolding proj by blast
qed

lemma PArr_M: "a \<in> PArr C \<Longrightarrow> M a"
  by (rule mem_M)

lemma PArr_eta: "a \<in> PArr C \<Longrightarrow> a = \<langle>\<langle>asrc a, atgt a\<rangle>, body a\<rangle>"
  by (rule PArrD(1))

lemma PArr_asrc [simp]: "a \<in> PArr C \<Longrightarrow> asrc a \<in> DOb C"
  by (rule PArrD(2))

lemma PArr_atgt [simp]: "a \<in> PArr C \<Longrightarrow> atgt a \<in> DOb C"
  by (rule PArrD(3))

lemma PArr_category_src [simp]: "a \<in> PArr C \<Longrightarrow> category (ix (asrc a))"
  by (rule DOb_category) (rule PArrD(2))

lemma PArr_category_tgt [simp]: "a \<in> PArr C \<Longrightarrow> category (ix (atgt a))"
  by (rule DOb_category) (rule PArrD(3))

lemma PArr_body_Lam: "a \<in> PArr C \<Longrightarrow> body a = (\<lambda>j\<in>Ob (ix (asrc a)). body a \<cdot> j)"
  by (rule PArrD(4))

lemma PArr_body_ccE:
  assumes "a \<in> PArr C" and "j \<in> Ob (ix (asrc a))"
  obtains v where "v \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)"
    and "body a \<cdot> j = cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v"
  using PArrD(5)[OF assms] by blast

lemma PArr_compat:
  assumes "a \<in> PArr C" and "u \<in> Arr (ix (asrc a))" and "M k" and "M f"
    and "\<langle>k, f\<rangle> \<in> body a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u"
  shows "\<langle>k, f \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u\<rangle> \<in> body a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u"
  by (rule PArrD(6)[OF assms])

lemma PArr_eqI:
  assumes a: "a \<in> PArr C" and b: "b \<in> PArr C"
    and src: "asrc a = asrc b" and tgt: "atgt a = atgt b"
    and body: "\<And>j. j \<in> Ob (ix (asrc a)) \<Longrightarrow> body a \<cdot> j = body b \<cdot> j"
  shows "a = b"
proof -
  have "body a = body b"
    by (rule fun_ext[OF PArr_body_Lam[OF a] PArr_body_Lam[OF b, folded src] body])
  have "a = \<langle>\<langle>asrc a, atgt a\<rangle>, body a\<rangle>"
    using a by (rule PArr_eta)
  also have "\<dots> = \<langle>\<langle>asrc b, atgt b\<rangle>, body b\<rangle>"
    by (simp only: src tgt \<open>body a = body b\<close>)
  also have "\<dots> = b"
    using b by (rule PArr_eta[symmetric])
  finally show ?thesis .
qed

subsection \<open>What being a component gives\<close>

text \<open>
  For an arrow \<open>a\<close> and an object \<open>j\<close> of its source, \<open>body a \<cdot> j\<close> is a component of the comma
  graph \<open>(dg (asrc a) \<cdot>\<^sub>o j \<down> dg (atgt a))\<close>: it has an element, its elements are vertices, any two
  are connected, it is closed under connectedness, and it is the component of each of its
  elements. Only the first needs no smallness.
\<close>

lemma PArr_obj [simp]: "a \<in> PArr C \<Longrightarrow> j \<in> Ob (ix (asrc a)) \<Longrightarrow> dg (asrc a) \<cdot>\<^sub>o j \<in> Ob C"
  by (rule DOb_dg_obj[OF PArr_asrc])

lemma PArr_body_ex:
  assumes "a \<in> PArr C" and "j \<in> Ob (ix (asrc a))"
  obtains k f where "\<langle>k, f\<rangle> \<in> body a \<cdot> j" and "M k" and "M f" and "k \<in> Ob (ix (atgt a))"
    and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j" and "tgt\<^bsub>C\<^esub> f = dg (atgt a) \<cdot>\<^sub>o k"
proof -
  obtain v where v: "v \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)"
    and eq: "body a \<cdot> j = cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v"
    using assms by (rule PArr_body_ccE)
  obtain k f where kf: "v = \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix (atgt a))" and f: "f \<in> Arr C"
    "src\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> f = dg (atgt a) \<cdot>\<^sub>o k"
    using v by (rule comma_vertsE)
  have "\<langle>k, f\<rangle> \<in> body a \<cdot> j"
    unfolding eq kf by simp
  then show ?thesis
    by (rule that[OF _ mem_M[OF k] mem_M[OF f(1)] k f])
qed

lemma PArr_body_vert:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C"
    and j: "j \<in> Ob (ix (asrc a))" and v: "v \<in> body a \<cdot> j"
  shows "v \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)"
proof -
  obtain v0 where v0: "v0 \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)"
    and eq: "body a \<cdot> j = cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v0"
    using a j by (rule PArr_body_ccE)
  have "conn (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v0 v"
    using v unfolding eq by simp
  then show ?thesis
    by (rule cgraph_conn_verts[OF C ls PArr_atgt[OF a] PArr_obj[OF a j] v0])
qed

lemma PArr_body_memE:
  assumes "category C" and "locally_small C" and "a \<in> PArr C"
    and "j \<in> Ob (ix (asrc a))" and "v \<in> body a \<cdot> j"
  obtains k f where "v = \<langle>k, f\<rangle>" and "M k" and "M f" and "k \<in> Ob (ix (atgt a))"
    and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j" and "tgt\<^bsub>C\<^esub> f = dg (atgt a) \<cdot>\<^sub>o k"
proof -
  obtain k f where v: "v = \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix (atgt a))" and f: "f \<in> Arr C"
    "src\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> f = dg (atgt a) \<cdot>\<^sub>o k"
    using PArr_body_vert[OF assms] by (rule comma_vertsE)
  show ?thesis
    by (rule that[OF v mem_M[OF k] mem_M[OF f(1)] k f])
qed

lemma PArr_body_pair:
  assumes "category C" and "locally_small C" and "a \<in> PArr C"
    and "j \<in> Ob (ix (asrc a))" and "\<langle>k, f\<rangle> \<in> body a \<cdot> j" and "M k" and "M f"
  shows "k \<in> Ob (ix (atgt a))" and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j"
    and "tgt\<^bsub>C\<^esub> f = dg (atgt a) \<cdot>\<^sub>o k"
  using PArr_body_vert[OF assms(1-5)] assms(6,7) by simp_all

lemma PArr_body_conn:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C"
    and j: "j \<in> Ob (ix (asrc a))" and v: "v \<in> body a \<cdot> j" and w: "w \<in> body a \<cdot> j"
  shows "conn (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v w"
proof -
  let ?E = "cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)"
  obtain v0 where v0: "v0 \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)" and eq: "body a \<cdot> j = cc ?E v0"
    using a j by (rule PArr_body_ccE)
  have E: "M ?E"
    using C ls a j by simp
  have "conn ?E v0 v" and "conn ?E v0 w"
    using v w unfolding eq by simp_all
  then show ?thesis
    using conn_sym[OF E mem_M[OF v0]] conn_trans by blast
qed

lemma PArr_body_closed:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C"
    and j: "j \<in> Ob (ix (asrc a))" and v: "v \<in> body a \<cdot> j"
    and vw: "conn (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v w"
  shows "w \<in> body a \<cdot> j"
proof -
  let ?E = "cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)"
  obtain v0 where "v0 \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)" and eq: "body a \<cdot> j = cc ?E v0"
    using a j by (rule PArr_body_ccE)
  have E: "M ?E"
    using C ls a j by simp
  have "conn ?E v0 v"
    using v unfolding eq by simp
  then have "conn ?E v0 w"
    using vw by (rule conn_trans)
  moreover have "M w"
    using conn_M[OF E mem_M[OF v] vw] .
  ultimately show ?thesis
    unfolding eq by simp
qed

lemma PArr_body_eq_cc:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C"
    and j: "j \<in> Ob (ix (asrc a))" and v: "v \<in> body a \<cdot> j"
  shows "body a \<cdot> j = cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) v"
proof -
  let ?E = "cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)"
  obtain v0 where v0: "v0 \<in> cverts C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)" and eq: "body a \<cdot> j = cc ?E v0"
    using a j by (rule PArr_body_ccE)
  have E: "M ?E"
    using C ls a j by simp
  have "conn ?E v0 v"
    using v unfolding eq by simp
  then have "cc ?E v0 = cc ?E v"
    by (rule cc_eq[OF E mem_M[OF v0]])
  then show ?thesis
    using eq by simp
qed

subsection \<open>The category structure read off\<close>

text \<open>
  The six components of \<open>PSh C\<close>, with the four maps applied at members of their domains.
  Composition needs no composability hypothesis: \<open>Pcomp\<close> is applied to any pair of arrows.
\<close>

lemma M_Pid [simp]: "M (Pid C X)"
  by (simp add: Pid_def)

lemma M_Pcomp [simp]: "M (Pcomp C b a)"
  by (simp add: Pcomp_def)

lemma PSh_Ob [simp]: "Ob (PSh C) = DOb C"
  by (simp add: PSh_def)

lemma PSh_Arr [simp]: "Arr (PSh C) = PArr C"
  by (simp add: PSh_def)

lemma PSh_src [simp]: "a \<in> PArr C \<Longrightarrow> src\<^bsub>PSh C\<^esub> a = asrc a"
  by (simp add: PSh_def)

lemma PSh_tgt [simp]: "a \<in> PArr C \<Longrightarrow> tgt\<^bsub>PSh C\<^esub> a = atgt a"
  by (simp add: PSh_def)

lemma PSh_id [simp]: "X \<in> DOb C \<Longrightarrow> id\<^bsub>PSh C\<^esub> X = Pid C X"
  by (simp add: PSh_def)

lemma PSh_comp [simp]: "a \<in> PArr C \<Longrightarrow> b \<in> PArr C \<Longrightarrow> b \<circ>\<^bsub>PSh C\<^esub> a = Pcomp C b a"
  by (simp add: PSh_def mem_M)

subsection \<open>Identities\<close>

text \<open>
  The projections of \<open>Pid C X\<close>. The body is not a simp rule, so that \<open>Pid_body_app\<close> can fire;
  it needs the component to be a set. The identity at \<open>X\<close> is an arrow: an arrow \<open>u : j \<rightarrow> j'\<close> of
  the index category joins \<open>\<langle>j, id\<rangle>\<close> to \<open>\<langle>j', dg X \<cdot>\<^sub>a u\<rangle>\<close>, and precomposing with \<open>dg X \<cdot>\<^sub>a u\<close> carries
  the component of \<open>\<langle>j', id\<rangle>\<close> to the component of \<open>\<langle>j', dg X \<cdot>\<^sub>a u\<rangle>\<close>.
\<close>

lemma asrc_Pid [simp]: "M X \<Longrightarrow> asrc (Pid C X) = X"
  by (simp add: Pid_def)

lemma atgt_Pid [simp]: "M X \<Longrightarrow> atgt (Pid C X) = X"
  by (simp add: Pid_def)

lemma body_Pid:
  "body (Pid C X) = (\<lambda>j\<in>Ob (ix X). cc (cgraph C X (dg X \<cdot>\<^sub>o j)) \<langle>j, id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j)\<rangle>)"
  by (simp add: Pid_def)

lemma Pid_body_app [simp]:
  assumes "category C" and "locally_small C" and "X \<in> DOb C" and "j \<in> Ob (ix X)"
  shows "body (Pid C X) \<cdot> j = cc (cgraph C X (dg X \<cdot>\<^sub>o j)) \<langle>j, id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j)\<rangle>"
  using assms by (simp add: body_Pid)

lemma Pid_PArr [simp]:
  assumes C: "category C" and ls: "locally_small C" and X: "X \<in> DOb C"
  shows "Pid C X \<in> PArr C"
proof -
  let ?F = "dg X"
  have FX: "is_functor ?F (ix X) C"
    using X by (rule DOb_functor)
  have cX: "category (ix X)"
    using X by simp
  show ?thesis
    unfolding Pid_def
  proof (rule PArr_LamI[OF C ls X X])
    show "dcls (\<lambda>j. cc (cgraph C X (?F \<cdot>\<^sub>o j)) \<langle>j, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)\<rangle>)"
      by dfn
    show "\<exists>\<^sub>s v. v \<in> cverts C X (?F \<cdot>\<^sub>o j) \<and>
        cc (cgraph C X (?F \<cdot>\<^sub>o j)) \<langle>j, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)\<rangle> = cc (cgraph C X (?F \<cdot>\<^sub>o j)) v"
      if j: "j \<in> Ob (ix X)" for j
    proof -
      have "\<langle>j, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)\<rangle> \<in> cverts C X (?F \<cdot>\<^sub>o j)"
        using C X j by (simp add: mem_M)
      then show ?thesis
        using M_opair by blast
    qed
    show "\<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<in> cc (cgraph C X (?F \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> u)) \<langle>src\<^bsub>ix X\<^esub> u, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> u)\<rangle>"
      if u: "u \<in> Arr (ix X)" and "M k" and "M f"
        and kf: "\<langle>k, f\<rangle> \<in> cc (cgraph C X (?F \<cdot>\<^sub>o tgt\<^bsub>ix X\<^esub> u)) \<langle>tgt\<^bsub>ix X\<^esub> u, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o tgt\<^bsub>ix X\<^esub> u)\<rangle>"
      for u k f
    proof -
      let ?s = "src\<^bsub>ix X\<^esub> u" and ?t = "tgt\<^bsub>ix X\<^esub> u"
      let ?Es = "cgraph C X (?F \<cdot>\<^sub>o ?s)"
      have st: "?s \<in> Ob (ix X)" "?t \<in> Ob (ix X)"
        using cX u by simp_all
      have Fu: "?F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?s" "tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?t"
        using X u by simp_all
      have c1: "conn (cgraph C X (?F \<cdot>\<^sub>o ?t)) \<langle>?t, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?t)\<rangle> \<langle>k, f\<rangle>"
        using kf by simp
      have "conn ?Es \<langle>?t, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?t) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle>"
        using comma_conn_precomp[OF M_ix ls cX C FX Fu(1) Fu(3) M_tgt M_idt \<open>M k\<close> \<open>M f\<close> c1]
        unfolding Fu(2) .
      moreover have "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?t) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u = ?F \<cdot>\<^sub>a u"
        using C Fu by simp
      ultimately have c2: "conn ?Es \<langle>?t, ?F \<cdot>\<^sub>a u\<rangle> \<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle>"
        by simp
      have ids: "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s) \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)) = ?F \<cdot>\<^sub>o ?s"
        "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)) = ?F \<cdot>\<^sub>o ?s"
        using C X st by simp_all
      have "\<langle>\<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>, \<langle>?t, ?F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>\<rangle> \<in> ?Es"
        by (rule comma_edgesI[OF u ids])
      moreover have "?F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s) = ?F \<cdot>\<^sub>a u"
        using C Fu by simp
      ultimately have "\<langle>\<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>, \<langle>?t, ?F \<cdot>\<^sub>a u\<rangle>\<rangle> \<in> ?Es"
        by simp
      then have c3: "conn ?Es \<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle> \<langle>?t, ?F \<cdot>\<^sub>a u\<rangle>"
        by (rule conn_edge[OF _ M_opair M_opair])
      show ?thesis
        using conn_trans[OF c3 c2] by simp
    qed
  qed
qed

subsection \<open>Composites\<close>

text \<open>
  The projections of \<open>Pcomp C b a\<close>. Its value at an object \<open>j\<close> is a set when \<open>a\<close> and \<open>b\<close> are
  composable arrows: every \<open>\<langle>l, g \<circ> f\<rangle>\<close> is a vertex of the small graph \<open>(dg (asrc a) \<cdot>\<^sub>o j \<down> dg (atgt b))\<close>,
  and so is everything connected to it. That it is the component of any one \<open>\<langle>l, g \<circ> f\<rangle>\<close> is the
  key lemma of \<open>PSh_Category\<close>.
\<close>

lemma asrc_Pcomp [simp]: "asrc (Pcomp C b a) = asrc a"
  by (simp add: Pcomp_def)

lemma atgt_Pcomp [simp]: "atgt (Pcomp C b a) = atgt b"
  by (simp add: Pcomp_def)

lemma body_Pcomp:
  "body (Pcomp C b a) =
    (\<lambda>j\<in>Ob (ix (asrc a)).
      \<lbrace>w. \<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> body a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> body b \<cdot> k \<and>
        conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w\<rbrace>)"
  by (simp add: Pcomp_def)

lemma Pcomp_vert:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C" and b: "b \<in> PArr C"
    and ab: "asrc b = atgt a" and j: "j \<in> Ob (ix (asrc a))"
    and kf: "\<langle>k, f\<rangle> \<in> body a \<cdot> j" and lg: "\<langle>l, g\<rangle> \<in> body b \<cdot> k"
    and "M k" and "M f" and "M l" and "M g"
  shows "\<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<in> cverts C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)"
proof -
  have k: "k \<in> Ob (ix (asrc b))" and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j"
    "tgt\<^bsub>C\<^esub> f = dg (asrc b) \<cdot>\<^sub>o k"
    using PArr_body_pair[OF C ls a j kf \<open>M k\<close> \<open>M f\<close>] ab by simp_all
  have l: "l \<in> Ob (ix (atgt b))" and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = dg (asrc b) \<cdot>\<^sub>o k"
    "tgt\<^bsub>C\<^esub> g = dg (atgt b) \<cdot>\<^sub>o l"
    using PArr_body_pair[OF C ls b k lg \<open>M l\<close> \<open>M g\<close>] by simp_all
  show ?thesis
    using C l f g \<open>M l\<close> by simp
qed

lemma Pcomp_set_sub:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C" and b: "b \<in> PArr C"
    and ab: "asrc b = atgt a" and j: "j \<in> Ob (ix (asrc a))"
  shows "\<lbrace>w. \<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> body a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> body b \<cdot> k \<and>
      conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w\<rbrace> \<subseteq>
    cverts C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)"
proof
  fix w
  assume "w \<in> \<lbrace>w. \<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> body a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> body b \<cdot> k \<and>
      conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w\<rbrace>"
  then obtain k f l g where "M k" "M f" "M l" "M g" and kf: "\<langle>k, f\<rangle> \<in> body a \<cdot> j"
    and lg: "\<langle>l, g\<rangle> \<in> body b \<cdot> k" and c: "conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w"
    by auto
  have "\<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<in> cverts C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)"
    by (rule Pcomp_vert[OF C ls a b ab j kf lg \<open>M k\<close> \<open>M f\<close> \<open>M l\<close> \<open>M g\<close>])
  then show "w \<in> cverts C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)"
    using c by (rule cgraph_conn_verts[OF C ls PArr_atgt[OF b] PArr_obj[OF a j]])
qed

lemma Pcomp_body_app:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C" and b: "b \<in> PArr C"
    and ab: "asrc b = atgt a" and j: "j \<in> Ob (ix (asrc a))"
  shows "body (Pcomp C b a) \<cdot> j =
    \<lbrace>w. \<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> body a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> body b \<cdot> k \<and>
      conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w\<rbrace>"
proof -
  have "M \<lbrace>w. \<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> body a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> body b \<cdot> k \<and>
      conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w\<rbrace>"
    using M_cverts[OF ls PArr_atgt[OF b] PArr_obj[OF a j]] Pcomp_set_sub[OF assms]
    by (rule M_subcls)
  then show ?thesis
    unfolding body_Pcomp using j by simp
qed

lemma mem_Pcomp_body:
  assumes "category C" and "locally_small C" and "a \<in> PArr C" and "b \<in> PArr C"
    and "asrc b = atgt a" and "j \<in> Ob (ix (asrc a))"
  shows "w \<in> body (Pcomp C b a) \<cdot> j \<longleftrightarrow>
    M w \<and> (\<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> body a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> body b \<cdot> k \<and>
      conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w)"
  unfolding Pcomp_body_app[OF assms] by simp

subsection \<open>The colimit functor\<close>

text \<open>
  \<open>colim_functor C\<close> is the identity on objects and sends \<open>a = (p, \<alpha>)\<close> to the family of the
  components of the \<open>\<langle>p \<cdot>\<^sub>o j, \<alpha> \<cdot> j\<rangle>\<close>. That family is an arrow: for \<open>u : j \<rightarrow> j'\<close>, precomposing
  with \<open>dg X \<cdot>\<^sub>a u\<close> carries the component of \<open>\<langle>p \<cdot>\<^sub>o j', \<alpha> \<cdot> j'\<rangle>\<close> to that of
  \<open>\<langle>p \<cdot>\<^sub>o j', \<alpha> \<cdot> j' \<circ> dg X \<cdot>\<^sub>a u\<rangle> = \<langle>p \<cdot>\<^sub>o j', dg Y \<cdot>\<^sub>a (p \<cdot>\<^sub>a u) \<circ> \<alpha> \<cdot> j\<rangle>\<close>, which the edge \<open>p \<cdot>\<^sub>a u\<close> joins
  to \<open>\<langle>p \<cdot>\<^sub>o j, \<alpha> \<cdot> j\<rangle>\<close>.
\<close>

lemma colim_functor_obj [simp]: "X \<in> DOb C \<Longrightarrow> colim_functor C \<cdot>\<^sub>o X = X"
  by (simp add: colim_functor_def mem_M)

lemma colim_functor_arr:
  "a \<in> DArr C \<Longrightarrow> colim_functor C \<cdot>\<^sub>a a =
    \<langle>\<langle>asrc a, atgt a\<rangle>,
      \<lambda>j\<in>Ob (ix (asrc a)). cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle>\<rangle>"
  by (simp add: colim_functor_def)

lemma asrc_colim_functor [simp]: "a \<in> DArr C \<Longrightarrow> asrc (colim_functor C \<cdot>\<^sub>a a) = asrc a"
  by (simp add: colim_functor_arr)

lemma atgt_colim_functor [simp]: "a \<in> DArr C \<Longrightarrow> atgt (colim_functor C \<cdot>\<^sub>a a) = atgt a"
  by (simp add: colim_functor_arr)

lemma colim_functor_body_app [simp]:
  assumes "category C" and "locally_small C" and "a \<in> DArr C" and "j \<in> Ob (ix (asrc a))"
  shows "body (colim_functor C \<cdot>\<^sub>a a) \<cdot> j =
    cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle>"
  using assms by (simp add: colim_functor_arr)

lemma colim_functor_PArr [simp]:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> DArr C"
  shows "colim_functor C \<cdot>\<^sub>a a \<in> PArr C"
proof -
  let ?X = "asrc a" and ?Y = "atgt a" and ?p = "afun a" and ?\<alpha> = "anat a"
  let ?F = "dg ?X" and ?G = "dg ?Y"
  have X: "?X \<in> DOb C" and Y: "?Y \<in> DOb C"
    using a by simp_all
  have FY: "is_functor ?G (ix ?Y) C"
    using Y by (rule DOb_functor)
  have p: "is_functor ?p (ix ?X) (ix ?Y)"
    using a by (rule DArr_functor)
  have cX: "category (ix ?X)" and cY: "category (ix ?Y)"
    using a by simp_all
  show ?thesis
    unfolding colim_functor_arr[OF a]
  proof (rule PArr_LamI[OF C ls X Y])
    show "dcls (\<lambda>j. cc (cgraph C ?Y (?F \<cdot>\<^sub>o j)) \<langle>?p \<cdot>\<^sub>o j, ?\<alpha> \<cdot> j\<rangle>)"
      by dfn
    show "\<exists>\<^sub>s v. v \<in> cverts C ?Y (?F \<cdot>\<^sub>o j) \<and>
        cc (cgraph C ?Y (?F \<cdot>\<^sub>o j)) \<langle>?p \<cdot>\<^sub>o j, ?\<alpha> \<cdot> j\<rangle> = cc (cgraph C ?Y (?F \<cdot>\<^sub>o j)) v"
      if j: "j \<in> Ob (ix ?X)" for j
    proof -
      have "\<langle>?p \<cdot>\<^sub>o j, ?\<alpha> \<cdot> j\<rangle> \<in> cverts C ?Y (?F \<cdot>\<^sub>o j)"
        using a j p by simp
      then show ?thesis
        using M_opair by blast
    qed
    show "\<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<in> cc (cgraph C ?Y (?F \<cdot>\<^sub>o src\<^bsub>ix ?X\<^esub> u)) \<langle>?p \<cdot>\<^sub>o src\<^bsub>ix ?X\<^esub> u, ?\<alpha> \<cdot> src\<^bsub>ix ?X\<^esub> u\<rangle>"
      if u: "u \<in> Arr (ix ?X)" and "M k" and "M f"
        and kf: "\<langle>k, f\<rangle> \<in> cc (cgraph C ?Y (?F \<cdot>\<^sub>o tgt\<^bsub>ix ?X\<^esub> u)) \<langle>?p \<cdot>\<^sub>o tgt\<^bsub>ix ?X\<^esub> u, ?\<alpha> \<cdot> tgt\<^bsub>ix ?X\<^esub> u\<rangle>"
      for u k f
    proof -
      let ?s = "src\<^bsub>ix ?X\<^esub> u" and ?t = "tgt\<^bsub>ix ?X\<^esub> u"
      let ?Es = "cgraph C ?Y (?F \<cdot>\<^sub>o ?s)"
      have st: "?s \<in> Ob (ix ?X)" "?t \<in> Ob (ix ?X)"
        using cX u by simp_all
      have Fu: "?F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?s" "tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?t"
        using X u by simp_all
      have c1: "conn (cgraph C ?Y (?F \<cdot>\<^sub>o ?t)) \<langle>?p \<cdot>\<^sub>o ?t, ?\<alpha> \<cdot> ?t\<rangle> \<langle>k, f\<rangle>"
        using kf by simp
      have "conn ?Es \<langle>?p \<cdot>\<^sub>o ?t, ?\<alpha> \<cdot> ?t \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle>"
        using comma_conn_precomp[OF M_ix ls cY C FY Fu(1) Fu(3) M_obj M_app \<open>M k\<close> \<open>M f\<close> c1]
        unfolding Fu(2) .
      then have c2: "conn ?Es \<langle>?p \<cdot>\<^sub>o ?t, ?G \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s\<rangle> \<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle>"
        unfolding DArr_anat_nat[OF a u] .
      have pu: "?p \<cdot>\<^sub>a u \<in> Arr (ix ?Y)" "src\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a u) = ?p \<cdot>\<^sub>o ?s"
        "tgt\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a u) = ?p \<cdot>\<^sub>o ?t"
        using p u by simp_all
      have \<alpha>s: "?\<alpha> \<cdot> ?s \<in> Arr C" "src\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?s) = ?F \<cdot>\<^sub>o ?s"
        "tgt\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?s) = ?G \<cdot>\<^sub>o src\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a u)"
        using a st pu by simp_all
      have "\<langle>\<langle>?p \<cdot>\<^sub>o ?s, ?\<alpha> \<cdot> ?s\<rangle>, \<langle>?p \<cdot>\<^sub>o ?t, ?G \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s\<rangle>\<rangle> \<in> ?Es"
        using comma_edgesI[OF pu(1) \<alpha>s] unfolding pu(2,3) .
      then have c3: "conn ?Es \<langle>?p \<cdot>\<^sub>o ?s, ?\<alpha> \<cdot> ?s\<rangle> \<langle>?p \<cdot>\<^sub>o ?t, ?G \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s\<rangle>"
        by (rule conn_edge[OF _ M_opair M_opair])
      show ?thesis
        using conn_trans[OF c3 c2] by simp
    qed
  qed
qed

end
