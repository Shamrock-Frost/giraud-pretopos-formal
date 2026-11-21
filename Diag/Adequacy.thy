section \<open>The category PSh C is the category of small presheaves\<close>

theory Adequacy
  imports Colim_Functor
begin

text \<open>
  \<open>PSh C\<close> was defined by a formula for its morphisms, not as a category of presheaves, because
  the small presheaves on a proper class do not form a class. This theory states what ties it
  to presheaves. Nothing here is used by the localization theorem.

  Fix a diagram \<open>X = \<langle>J, F\<rangle>\<close>. The presheaf \<open>colim\<^sub>j y(F j)\<close> is computed pointwise: its value at
  an object \<open>c\<close> of \<open>C\<close> is the colimit of the sets \<open>Hom(c, F j)\<close>, that is the set of connected
  components of the comma category \<open>(c \<down> F)\<close>. That set is \<open>elts C X c\<close>. An arrow \<open>u : c' \<rightarrow> c\<close>
  acts by precomposition, \<open>[j, f] \<mapsto> [j, f \<circ> u]\<close>; that is \<open>pre C X u\<close>.

  A morphism \<open>\<phi> : X \<rightarrow> Y\<close> of \<open>PSh C\<close> acts on these presheaves by \<open>[j, f] \<mapsto> \<phi>\<^sub>j \<circ> f\<close>; that is
  \<open>act C \<phi> c\<close>. The theorems say: each \<open>elts C X\<close> with \<open>pre C X\<close> is a presheaf of sets on \<open>C\<close>;
  \<open>act C \<phi>\<close> is a natural transformation; this is functorial in \<open>\<phi>\<close>; and every natural
  transformation between two such presheaves is \<open>act C \<phi>\<close> for exactly one \<open>\<phi>\<close>. So \<open>X \<mapsto> elts C X\<close>
  is a full and faithful functor from \<open>PSh C\<close> to presheaves on \<open>C\<close>, and its image is the
  presheaves that are small colimits of representables, which are the small presheaves.
  Finally \<open>colim_functor C\<close> acts as the map of colimits induced by a morphism of diagrams.

  A natural transformation here is a class \<open>\<eta>\<close>, with component \<open>\<eta> \<cdot> \<langle>c, \<kappa>\<rangle>\<close> at an object \<open>c\<close> and
  an element \<open>\<kappa>\<close>; it is quantified over as a class.
\<close>

definition elts :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "elts C X c = \<lbrace>\<kappa>. \<exists>\<^sub>s v. v \<in> cverts C X c \<and> \<kappa> = cc (cgraph C X c) v\<rbrace>"

definition pre :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "pre C X u \<kappa> =
    \<lbrace>w. \<exists>\<^sub>s k f. \<langle>k, f\<rangle> \<in> \<kappa> \<and> conn (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> w\<rbrace>"

definition act :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "act C \<phi> c \<kappa> =
    \<lbrace>w. \<exists>\<^sub>s j f l g. \<langle>j, f\<rangle> \<in> \<kappa> \<and> \<langle>l, g\<rangle> \<in> body \<phi> \<cdot> j \<and> conn (cgraph C (atgt \<phi>) c) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w\<rbrace>"

lemma dcls_elts [dfn_rules]:
  "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dcls c \<Longrightarrow> dcls (\<lambda>x. elts (C x) (X x) (c x))"
  unfolding elts_def by dfn

lemma dcls_pre [dfn_rules]:
  "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dcls u \<Longrightarrow> dcls \<kappa> \<Longrightarrow> dcls (\<lambda>x. pre (C x) (X x) (u x) (\<kappa> x))"
  unfolding pre_def by dfn

lemma dcls_act [dfn_rules]:
  "dcls C \<Longrightarrow> dcls \<phi> \<Longrightarrow> dcls c \<Longrightarrow> dcls \<kappa> \<Longrightarrow> dcls (\<lambda>x. act (C x) (\<phi> x) (c x) (\<kappa> x))"
  unfolding act_def by dfn

subsection \<open>Reading elements and precomposition\<close>

text \<open>
  The two comprehensions opened. An element is the component of a vertex; precomposition with
  \<open>u\<close> collects everything connected to some \<open>\<langle>k, f \<circ> u\<rangle>\<close> with \<open>\<langle>k, f\<rangle>\<close> in the element.
\<close>

lemma mem_elts:
  "\<kappa> \<in> elts C X c \<longleftrightarrow> M \<kappa> \<and> (\<exists>\<^sub>s v. v \<in> cverts C X c \<and> \<kappa> = cc (cgraph C X c) v)"
  unfolding elts_def by simp

lemma eltsE:
  assumes "\<kappa> \<in> elts C X c"
  obtains k f where "\<kappa> = cc (cgraph C X c) \<langle>k, f\<rangle>" and "k \<in> Ob (ix X)" and "f \<in> Arr C"
    and "src\<^bsub>C\<^esub> f = c" and "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
proof -
  obtain v where v: "v \<in> cverts C X c" and \<kappa>: "\<kappa> = cc (cgraph C X c) v"
    using assms unfolding mem_elts by blast
  from v obtain k f where vkf: "v = \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix X)" and f: "f \<in> Arr C"
    "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
    by (rule comma_vertsE)
  have "\<kappa> = cc (cgraph C X c) \<langle>k, f\<rangle>"
    using \<kappa> vkf by simp
  then show ?thesis
    by (rule that[OF _ k f])
qed

lemma mem_pre:
  "w \<in> pre C X u \<kappa> \<longleftrightarrow>
    M w \<and> (\<exists>\<^sub>s k f. \<langle>k, f\<rangle> \<in> \<kappa> \<and> conn (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> w)"
  unfolding pre_def by simp

text \<open>
  For a diagram \<open>X\<close> in a locally small category: the elements at \<open>c\<close> form a set; the component
  of a vertex is an element; every member of an element is a vertex whose component is that
  element; and precomposition sends the component of \<open>\<langle>k, f\<rangle>\<close> to the component of \<open>\<langle>k, f \<circ> u\<rangle>\<close>.
  Each lemma below carries the three hypotheses \<open>category C\<close>, \<open>locally_small C\<close>, \<open>X \<in> DOb C\<close>
  first.
\<close>

context
  fixes C X
  assumes C: "category C" and lsC: "locally_small C" and X: "X \<in> DOb C"
begin

private lemma cX: "category (ix X)"
  using X by simp

private lemma FX: "is_functor (dg X) (ix X) C"
  using X by (rule DOb_functor)

lemma M_elts:
  assumes c: "c \<in> Ob C"
  shows "M (elts C X c)"
proof -
  have "M (cverts C X c)"
    using M_ix lsC c FX by (rule M_comma_verts)
  then show ?thesis
    unfolding elts_def by (rule M_replace) dfn
qed

lemma elts_ccI:
  assumes c: "c \<in> Ob C" and v: "v \<in> cverts C X c"
  shows "cc (cgraph C X c) v \<in> elts C X c"
proof -
  have "M (cc (cgraph C X c) v)"
    using M_ix lsC c cX C FX mem_M[OF v] by (rule M_comma_cc)
  then show ?thesis
    unfolding mem_elts using v mem_M[OF v] by blast
qed

lemma elts_member:
  assumes \<kappa>: "\<kappa> \<in> elts C X c" and w: "w \<in> \<kappa>"
  shows "w \<in> cverts C X c" and "\<kappa> = cc (cgraph C X c) w"
proof -
  obtain k f where \<kappa>eq: "\<kappa> = cc (cgraph C X c) \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix X)"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
    using \<kappa> by (rule eltsE)
  have c: "c \<in> Ob C"
    using cat_src[OF C f(1)] f(2) by simp
  have v: "\<langle>k, f\<rangle> \<in> cverts C X c"
    using k f by (simp add: mem_M)
  have cw: "conn (cgraph C X c) \<langle>k, f\<rangle> w"
    using w \<kappa>eq by simp
  show "w \<in> cverts C X c"
    using M_ix lsC c cX C FX v cw by (rule comma_conn_verts)
  show "\<kappa> = cc (cgraph C X c) w"
    unfolding \<kappa>eq by (rule cc_eq[OF M_comma_edges[OF M_ix lsC c cX C FX] _ cw]) simp
qed

lemma pre_cc:
  assumes u: "u \<in> Arr C" and k: "k \<in> Ob (ix X)"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
  shows "pre C X u (cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>k, f\<rangle>) = cc (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
proof -
  let ?E = "cgraph C X (tgt\<^bsub>C\<^esub> u)" and ?E' = "cgraph C X (src\<^bsub>C\<^esub> u)"
  have "M k" and "M f"
    using k f by (simp_all add: mem_M)
  have self: "\<langle>k, f\<rangle> \<in> cc ?E \<langle>k, f\<rangle>"
    by simp
  show ?thesis
  proof (rule cls_eqI)
    fix w
    assume "w \<in> pre C X u (cc ?E \<langle>k, f\<rangle>)"
    then obtain k' f' where "M w" and "M k'" and "M f'" and kf': "\<langle>k', f'\<rangle> \<in> cc ?E \<langle>k, f\<rangle>"
      and cw: "conn ?E' \<langle>k', f' \<circ>\<^bsub>C\<^esub> u\<rangle> w"
      unfolding mem_pre by blast
    have "conn ?E \<langle>k, f\<rangle> \<langle>k', f'\<rangle>"
      using kf' by simp
    then have "conn ?E' \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> \<langle>k', f' \<circ>\<^bsub>C\<^esub> u\<rangle>"
      by (rule comma_conn_precomp[OF M_ix lsC cX C FX u refl \<open>M k\<close> \<open>M f\<close> \<open>M k'\<close> \<open>M f'\<close>])
    then have "conn ?E' \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> w"
      using cw by (rule conn_trans)
    with \<open>M w\<close> show "w \<in> cc ?E' \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
      by simp
  next
    fix w
    assume "w \<in> cc ?E' \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
    then have "M w" and "conn ?E' \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> w"
      by simp_all
    then show "w \<in> pre C X u (cc ?E \<langle>k, f\<rangle>)"
      unfolding mem_pre using self \<open>M k\<close> \<open>M f\<close> by blast
  qed
qed

lemma pre_member:
  assumes u: "u \<in> Arr C" and \<kappa>: "\<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u)" and kf: "\<langle>k, f\<rangle> \<in> \<kappa>"
    and "M k" and "M f"
  shows "pre C X u \<kappa> = cc (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
proof -
  have v: "\<langle>k, f\<rangle> \<in> cverts C X (tgt\<^bsub>C\<^esub> u)"
    using \<kappa> kf by (rule elts_member)
  have \<kappa>eq: "\<kappa> = cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>k, f\<rangle>"
    using \<kappa> kf by (rule elts_member)
  have k: "k \<in> Ob (ix X)" and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
    using v \<open>M k\<close> \<open>M f\<close> by simp_all
  show ?thesis
    unfolding \<kappa>eq using u k f by (rule pre_cc)
qed

lemma pre_elts:
  assumes u: "u \<in> Arr C" and \<kappa>: "\<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
  shows "pre C X u \<kappa> \<in> elts C X (src\<^bsub>C\<^esub> u)"
proof -
  obtain k f where \<kappa>eq: "\<kappa> = cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix X)"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
    using \<kappa> by (rule eltsE)
  have su: "src\<^bsub>C\<^esub> u \<in> Ob C"
    using C u by simp
  have "\<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> \<in> cverts C X (src\<^bsub>C\<^esub> u)"
    using C u k f by (simp add: mem_M)
  then have "cc (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> \<in> elts C X (src\<^bsub>C\<^esub> u)"
    by (rule elts_ccI[OF su])
  then show ?thesis
    unfolding \<kappa>eq pre_cc[OF u k f] .
qed

end

subsection \<open>Each diagram gives a presheaf of sets\<close>

theorem elts_presheaf:
  assumes "category C" and "locally_small C" and "X \<in> DOb C"
  shows "\<forall>\<^sub>s c. c \<in> Ob C \<longrightarrow> M (elts C X c)"
    and "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u) \<longrightarrow> pre C X u \<kappa> \<in> elts C X (src\<^bsub>C\<^esub> u)"
    and "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> pre C X (id\<^bsub>C\<^esub> c) \<kappa> = \<kappa>"
    and "\<forall>\<^sub>s u v \<kappa>. u \<in> Arr C \<longrightarrow> v \<in> Arr C \<longrightarrow> src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u \<longrightarrow> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> v) \<longrightarrow>
      pre C X (v \<circ>\<^bsub>C\<^esub> u) \<kappa> = pre C X u (pre C X v \<kappa>)"
proof -
  note C = assms(1)
  show "\<forall>\<^sub>s c. c \<in> Ob C \<longrightarrow> M (elts C X c)"
    using M_elts[OF assms] by blast
  show "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u) \<longrightarrow> pre C X u \<kappa> \<in> elts C X (src\<^bsub>C\<^esub> u)"
    using pre_elts[OF assms] by blast
  show "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> pre C X (id\<^bsub>C\<^esub> c) \<kappa> = \<kappa>"
  proof (intro allI impI)
    fix c \<kappa>
    assume "M c" "M \<kappa>" and c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C X c"
    obtain k f where \<kappa>eq: "\<kappa> = cc (cgraph C X c) \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix X)"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
      using \<kappa> by (rule eltsE)
    have i: "id\<^bsub>C\<^esub> c \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c) = c" "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c) = c"
      using C c by simp_all
    have f': "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c)" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
      using f i by simp_all
    have "f \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> c = f"
      using C f by simp
    then show "pre C X (id\<^bsub>C\<^esub> c) \<kappa> = \<kappa>"
      using pre_cc[OF assms i(1) k f'] i by (simp add: \<kappa>eq)
  qed
  show "\<forall>\<^sub>s u v \<kappa>. u \<in> Arr C \<longrightarrow> v \<in> Arr C \<longrightarrow> src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u \<longrightarrow>
      \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> v) \<longrightarrow> pre C X (v \<circ>\<^bsub>C\<^esub> u) \<kappa> = pre C X u (pre C X v \<kappa>)"
  proof (intro allI impI)
    fix u v \<kappa>
    assume "M u" "M v" "M \<kappa>" and u: "u \<in> Arr C" and v: "v \<in> Arr C"
      and uv: "src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u" and \<kappa>: "\<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> v)"
    obtain k f where \<kappa>eq: "\<kappa> = cc (cgraph C X (tgt\<^bsub>C\<^esub> v)) \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix X)"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> v" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
      using \<kappa> by (rule eltsE)
    have vu: "v \<circ>\<^bsub>C\<^esub> u \<in> Arr C" "src\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u) = src\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u) = tgt\<^bsub>C\<^esub> v"
      using C u v uv by simp_all
    have fv: "f \<circ>\<^bsub>C\<^esub> v \<in> Arr C" "src\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> v) = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> v) = dg X \<cdot>\<^sub>o k"
      using C v f uv by simp_all
    have f_vu: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u)" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
      using f vu by simp_all
    have e1: "pre C X v \<kappa> = cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> v\<rangle>"
      unfolding \<kappa>eq pre_cc[OF assms v k f] uv by (rule refl)
    have e2: "pre C X u (cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> v\<rangle>) =
        cc (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>k, (f \<circ>\<^bsub>C\<^esub> v) \<circ>\<^bsub>C\<^esub> u\<rangle>"
      using u k fv by (rule pre_cc[OF assms])
    have e3: "pre C X (v \<circ>\<^bsub>C\<^esub> u) \<kappa> = cc (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u)\<rangle>"
      using pre_cc[OF assms vu(1) k f_vu] vu by (simp add: \<kappa>eq)
    have assoc: "(f \<circ>\<^bsub>C\<^esub> v) \<circ>\<^bsub>C\<^esub> u = f \<circ>\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u)"
      by (rule cat_assoc[OF C u v f(1) uv f(2), symmetric])
    show "pre C X (v \<circ>\<^bsub>C\<^esub> u) \<kappa> = pre C X u (pre C X v \<kappa>)"
      by (simp only: e1 e2 e3 assoc)
  qed
qed

text \<open>The elements are the classes \<open>[j, f]\<close>, and precomposition is \<open>[j, f] \<mapsto> [j, f \<circ> u]\<close>.\<close>

theorem elts_classes:
  assumes "category C" and "locally_small C" and "X \<in> DOb C" and "c \<in> Ob C"
  shows "\<forall>\<^sub>s \<kappa>. \<kappa> \<in> elts C X c \<longleftrightarrow>
      (\<exists>\<^sub>s j f. j \<in> Ob (ix X) \<and> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<and> \<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>)"
    and "\<forall>\<^sub>s u j f. u \<in> Hom C c' c \<longrightarrow> j \<in> Ob (ix X) \<longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<longrightarrow>
      pre C X u (cc (cgraph C X c) \<langle>j, f\<rangle>) = cc (cgraph C X c') \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
proof -
  note base = assms(1-3)
  show "\<forall>\<^sub>s \<kappa>. \<kappa> \<in> elts C X c \<longleftrightarrow>
      (\<exists>\<^sub>s j f. j \<in> Ob (ix X) \<and> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<and> \<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>)"
  proof (intro allI impI iffI)
    fix \<kappa>
    assume "M \<kappa>" and \<kappa>: "\<kappa> \<in> elts C X c"
    obtain k f where \<kappa>eq: "\<kappa> = cc (cgraph C X c) \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix X)"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o k"
      using \<kappa> by (rule eltsE)
    have "M k" and "M f"
      using k f by (simp_all add: mem_M)
    have hf: "f \<in> Hom C c (dg X \<cdot>\<^sub>o k)"
      using f by simp
    show "\<exists>\<^sub>s j f. j \<in> Ob (ix X) \<and> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<and> \<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>"
      using \<open>M k\<close> \<open>M f\<close> k hf \<kappa>eq by blast
  next
    fix \<kappa>
    assume "M \<kappa>"
      and "\<exists>\<^sub>s j f. j \<in> Ob (ix X) \<and> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<and> \<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>"
    then obtain j f where "M j" and "M f" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
      and \<kappa>eq: "\<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>"
      by blast
    have "\<langle>j, f\<rangle> \<in> cverts C X c"
      using \<open>M j\<close> \<open>M f\<close> j f by simp
    then show "\<kappa> \<in> elts C X c"
      unfolding \<kappa>eq by (rule elts_ccI[OF base assms(4)])
  qed
  show "\<forall>\<^sub>s u j f. u \<in> Hom C c' c \<longrightarrow> j \<in> Ob (ix X) \<longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<longrightarrow>
      pre C X u (cc (cgraph C X c) \<langle>j, f\<rangle>) = cc (cgraph C X c') \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
  proof (intro allI impI)
    fix u j f
    assume "M u" "M j" "M f" and u: "u \<in> Hom C c' c" and j: "j \<in> Ob (ix X)"
      and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
    have ua: "u \<in> Arr C" "src\<^bsub>C\<^esub> u = c'" "tgt\<^bsub>C\<^esub> u = c"
      using u by simp_all
    have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
      using f ua by simp_all
    show "pre C X u (cc (cgraph C X c) \<langle>j, f\<rangle>) = cc (cgraph C X c') \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
      using pre_cc[OF base ua(1) j fa] unfolding ua(2,3) .
  qed
qed

subsection \<open>Reading the action\<close>

text \<open>
  The comprehension of \<open>act\<close> opened, and the computation rule: for an arrow \<open>\<phi>\<close> of \<open>PSh C\<close>, the
  action on the component of \<open>\<langle>j, f\<rangle>\<close> is the component of \<open>\<langle>l, g \<circ> f\<rangle>\<close> for any \<open>\<langle>l, g\<rangle>\<close> in
  \<open>body \<phi> \<cdot> j\<close>. That it does not depend on the choices is \<open>act_conn\<close>: along an edge
  \<open>\<langle>j, h\<rangle> \<rightarrow> \<langle>j', F e \<circ> h\<rangle>\<close> of \<open>(x \<down> F)\<close> the family \<open>\<phi>\<close> is compatible with \<open>e\<close>, and inside one
  component of \<open>(F j \<down> G)\<close> precomposition with \<open>f\<close> preserves connectedness.
\<close>

lemma mem_act:
  "w \<in> act C \<phi> c \<kappa> \<longleftrightarrow>
    M w \<and> (\<exists>\<^sub>s j f l g. \<langle>j, f\<rangle> \<in> \<kappa> \<and> \<langle>l, g\<rangle> \<in> body \<phi> \<cdot> j \<and>
      conn (cgraph C (atgt \<phi>) c) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w)"
  unfolding act_def by simp

context
  fixes C \<phi>
  assumes C: "category C" and ls: "locally_small C" and \<phi>: "\<phi> \<in> PArr C"
begin

private lemma X\<phi>: "asrc \<phi> \<in> DOb C"
  using \<phi> by simp

private lemma Y\<phi>: "atgt \<phi> \<in> DOb C"
  using \<phi> by simp

private lemma cY\<phi>: "category (ix (atgt \<phi>))"
  using \<phi> by simp

private lemma FY\<phi>: "is_functor (dg (atgt \<phi>)) (ix (atgt \<phi>)) C"
  using Y\<phi> by (rule DOb_functor)

lemma act_conn:
  assumes j: "j \<in> Ob (ix (asrc \<phi>))"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j"
    and lg: "\<langle>l, g\<rangle> \<in> body \<phi> \<cdot> j" and "M l" and "M g"
    and c': "conn (cgraph C (asrc \<phi>) x) \<langle>j, f\<rangle> \<langle>j', f'\<rangle>" and "M j'" and "M f'"
    and lg': "\<langle>l', g'\<rangle> \<in> body \<phi> \<cdot> j'" and "M l'" and "M g'"
  shows "conn (cgraph C (atgt \<phi>) x) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
proof -
  let ?X = "asrc \<phi>" and ?Y = "atgt \<phi>"
  let ?F = "dg ?X" and ?EX = "cgraph C ?X x" and ?EY = "cgraph C ?Y x"
  let ?P = "\<lambda>v. \<forall>\<^sub>s l1 g1. \<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> pfst v \<longrightarrow>
    conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> psnd v\<rangle>"
  have cX: "category (ix ?X)"
    using \<phi> by simp
  have xo: "x \<in> Ob C"
    using cat_src[OF C f(1)] f(2) by simp
  have "M j" and "M f"
    using j f by (simp_all add: mem_M)
  have "?P \<langle>j', f'\<rangle>"
  proof (rule conn_induct[OF M_cgraph[OF C ls X\<phi> xo] _ c'])
    show "M \<langle>j, f\<rangle>"
      by simp
    show "dfn ?P"
      by dfn
    show "?P \<langle>j, f\<rangle>"
    proof (intro allI impI)
      fix l1 g1
      assume "M l1" "M g1" and in1: "\<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> pfst \<langle>j, f\<rangle>"
      have in1': "\<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> j"
        using in1 \<open>M j\<close> \<open>M f\<close> by simp
      have "conn (cgraph C ?Y (?F \<cdot>\<^sub>o j)) \<langle>l, g\<rangle> \<langle>l1, g1\<rangle>"
        by (rule PArr_body_conn[OF C ls \<phi> j lg in1'])
      then have "conn (cgraph C ?Y (src\<^bsub>C\<^esub> f)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> f\<rangle>"
        by (rule comma_conn_precomp[OF M_ix ls cY\<phi> C FY\<phi> f(1) f(3) \<open>M l\<close> \<open>M g\<close> \<open>M l1\<close> \<open>M g1\<close>])
      then show "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> psnd \<langle>j, f\<rangle>\<rangle>"
        using f(2) \<open>M j\<close> \<open>M f\<close> by simp
    qed
  next
    fix a b
    assume ab: "M a" "M b" "\<langle>a, b\<rangle> \<in> ?EX" "conn ?EX \<langle>j, f\<rangle> a"
    from ab(3,1,2) obtain h e where a: "a = \<langle>src\<^bsub>ix ?X\<^esub> e, h\<rangle>"
      and b: "b = \<langle>tgt\<^bsub>ix ?X\<^esub> e, ?F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h\<rangle>" and e: "e \<in> Arr (ix ?X)"
      and h: "h \<in> Arr C" "src\<^bsub>C\<^esub> h = x" "tgt\<^bsub>C\<^esub> h = ?F \<cdot>\<^sub>o src\<^bsub>ix ?X\<^esub> e"
      by (rule comma_edge_pairE)
    let ?s = "src\<^bsub>ix ?X\<^esub> e" and ?t = "tgt\<^bsub>ix ?X\<^esub> e"
    have simps: "pfst a = ?s" "psnd a = h" "pfst b = ?t" "psnd b = ?F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h"
      unfolding a b using h(1) by (simp_all add: mem_M)
    have st: "?s \<in> Ob (ix ?X)" "?t \<in> Ob (ix ?X)"
      using cX e by simp_all
    have Fe: "?F \<cdot>\<^sub>a e \<in> Arr C" "src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a e) = tgt\<^bsub>C\<^esub> h" "tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a e) = ?F \<cdot>\<^sub>o ?t"
      using X\<phi> e h by simp_all
    text \<open>For \<open>\<langle>l1, g1\<rangle>\<close> in \<open>\<phi>\<close> at the target of \<open>e\<close>: compatibility and associativity.\<close>
    have at_t: "\<langle>l1, g1 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e\<rangle> \<in> body \<phi> \<cdot> ?s"
      and assoc: "g1 \<circ>\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h) = (g1 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> h"
      if "M l1" "M g1" and in1: "\<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> ?t" for l1 g1
    proof -
      show "\<langle>l1, g1 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e\<rangle> \<in> body \<phi> \<cdot> ?s"
        by (rule PArr_compat[OF \<phi> e that(1,2) in1])
      have g1: "g1 \<in> Arr C" "src\<^bsub>C\<^esub> g1 = ?F \<cdot>\<^sub>o ?t"
        using PArr_body_pair[OF C ls \<phi> st(2) in1 that(1,2)] by simp_all
      show "g1 \<circ>\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h) = (g1 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> h"
        using cat_assoc[OF C h(1) Fe(1) g1(1) Fe(2)] g1(2) Fe(3) by simp
    qed
    show "?P a \<longleftrightarrow> ?P b"
    proof
      assume Pa: "?P a"
      show "?P b"
      proof (intro allI impI)
        fix l1 g1
        assume "M l1" "M g1" and in1: "\<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> pfst b"
        have in1': "\<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> ?t"
          using in1 simps by simp
        have "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l1, (g1 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> psnd a\<rangle>"
          by (rule Pa[rule_format]) (use \<open>M l1\<close> at_t[OF \<open>M l1\<close> \<open>M g1\<close> in1'] simps in simp_all)
        then show "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> psnd b\<rangle>"
          using assoc[OF \<open>M l1\<close> \<open>M g1\<close> in1'] simps by simp
      qed
    next
      assume Pb: "?P b"
      show "?P a"
      proof (intro allI impI)
        fix l1 g1
        assume "M l1" "M g1" and in1: "\<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> pfst a"
        have in1': "\<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> ?s"
          using in1 simps by simp
        obtain l2 g2 where in2: "\<langle>l2, g2\<rangle> \<in> body \<phi> \<cdot> ?t" and "M l2" and "M g2"
          using \<phi> st(2) by (rule PArr_body_ex)
        have "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l2, g2 \<circ>\<^bsub>C\<^esub> psnd b\<rangle>"
          by (rule Pb[rule_format]) (use in2 \<open>M l2\<close> \<open>M g2\<close> simps in simp_all)
        then have "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l2, g2 \<circ>\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h)\<rangle>"
          unfolding simps .
        then have c1: "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l2, (g2 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> h\<rangle>"
          unfolding assoc[OF \<open>M l2\<close> \<open>M g2\<close> in2] .
        have "conn (cgraph C ?Y (?F \<cdot>\<^sub>o ?s)) \<langle>l2, g2 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e\<rangle> \<langle>l1, g1\<rangle>"
          by (rule PArr_body_conn[OF C ls \<phi> st(1) at_t[OF \<open>M l2\<close> \<open>M g2\<close> in2] in1'])
        then have "conn (cgraph C ?Y (src\<^bsub>C\<^esub> h)) \<langle>l2, (g2 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> h\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> h\<rangle>"
          by (rule comma_conn_precomp[OF M_ix ls cY\<phi> C FY\<phi> h(1) h(3) \<open>M l2\<close> M_ccomp \<open>M l1\<close> \<open>M g1\<close>])
        then have c2: "conn ?EY \<langle>l2, (g2 \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> h\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> h\<rangle>"
          unfolding h(2) .
        show "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> psnd a\<rangle>"
          using conn_trans[OF c1 c2] simps by simp
      qed
    qed
  qed
  then have "\<forall>\<^sub>s l1 g1. \<langle>l1, g1\<rangle> \<in> body \<phi> \<cdot> j' \<longrightarrow> conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> f'\<rangle>"
    using \<open>M j'\<close> \<open>M f'\<close> by simp
  then show ?thesis
    using lg' \<open>M l'\<close> \<open>M g'\<close> by blast
qed

lemma act_cc:
  assumes j: "j \<in> Ob (ix (asrc \<phi>))"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j"
    and lg: "\<langle>l, g\<rangle> \<in> body \<phi> \<cdot> j" and "M l" and "M g"
  shows "act C \<phi> x (cc (cgraph C (asrc \<phi>) x) \<langle>j, f\<rangle>) = cc (cgraph C (atgt \<phi>) x) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  let ?EX = "cgraph C (asrc \<phi>) x" and ?EY = "cgraph C (atgt \<phi>) x"
  have "M j" and "M f"
    using j f by (simp_all add: mem_M)
  show ?thesis
  proof (rule cls_eqI)
    fix w
    assume "w \<in> act C \<phi> x (cc ?EX \<langle>j, f\<rangle>)"
    then obtain j' f' l' g' where "M w" "M j'" "M f'" "M l'" "M g'"
      and in': "\<langle>j', f'\<rangle> \<in> cc ?EX \<langle>j, f\<rangle>" and lg': "\<langle>l', g'\<rangle> \<in> body \<phi> \<cdot> j'"
      and cw: "conn ?EY \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle> w"
      unfolding mem_act by blast
    have "conn ?EX \<langle>j, f\<rangle> \<langle>j', f'\<rangle>"
      using in' by simp
    then have "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
      using \<open>M j'\<close> \<open>M f'\<close> lg' \<open>M l'\<close> \<open>M g'\<close> by (rule act_conn[OF j f lg \<open>M l\<close> \<open>M g\<close>])
    then have "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w"
      using cw by (rule conn_trans)
    with \<open>M w\<close> show "w \<in> cc ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by simp
  next
    fix w
    assume "w \<in> cc ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
    then have "M w" and "conn ?EY \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w"
      by simp_all
    moreover have "\<langle>j, f\<rangle> \<in> cc ?EX \<langle>j, f\<rangle>"
      by simp
    ultimately show "w \<in> act C \<phi> x (cc ?EX \<langle>j, f\<rangle>)"
      unfolding mem_act using lg \<open>M j\<close> \<open>M f\<close> \<open>M l\<close> \<open>M g\<close> by blast
  qed
qed

lemma act_member:
  assumes \<kappa>: "\<kappa> \<in> elts C (asrc \<phi>) x" and jf: "\<langle>j, f\<rangle> \<in> \<kappa>" and "M j" and "M f"
    and lg: "\<langle>l, g\<rangle> \<in> body \<phi> \<cdot> j" and "M l" and "M g"
  shows "act C \<phi> x \<kappa> = cc (cgraph C (atgt \<phi>) x) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  have v: "\<langle>j, f\<rangle> \<in> cverts C (asrc \<phi>) x"
    using C ls X\<phi> \<kappa> jf by (rule elts_member)
  have \<kappa>eq: "\<kappa> = cc (cgraph C (asrc \<phi>) x) \<langle>j, f\<rangle>"
    using C ls X\<phi> \<kappa> jf by (rule elts_member)
  have j: "j \<in> Ob (ix (asrc \<phi>))" and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x"
    "tgt\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j"
    using v \<open>M j\<close> \<open>M f\<close> by simp_all
  show ?thesis
    unfolding \<kappa>eq using j f lg \<open>M l\<close> \<open>M g\<close> by (rule act_cc)
qed

lemma act_elts:
  assumes \<kappa>: "\<kappa> \<in> elts C (asrc \<phi>) x"
  shows "act C \<phi> x \<kappa> \<in> elts C (atgt \<phi>) x"
proof -
  obtain j f where \<kappa>eq: "\<kappa> = cc (cgraph C (asrc \<phi>) x) \<langle>j, f\<rangle>" and j: "j \<in> Ob (ix (asrc \<phi>))"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j"
    using \<kappa> by (rule eltsE)
  obtain l g where lg: "\<langle>l, g\<rangle> \<in> body \<phi> \<cdot> j" and "M l" and "M g" and l: "l \<in> Ob (ix (atgt \<phi>))"
    and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = dg (asrc \<phi>) \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> g = dg (atgt \<phi>) \<cdot>\<^sub>o l"
    using \<phi> j by (rule PArr_body_ex)
  have xo: "x \<in> Ob C"
    using cat_src[OF C f(1)] f(2) by simp
  have "\<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<in> cverts C (atgt \<phi>) x"
    using C l f g \<open>M l\<close> by simp
  then have "cc (cgraph C (atgt \<phi>) x) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<in> elts C (atgt \<phi>) x"
    by (rule elts_ccI[OF C ls Y\<phi> xo])
  then show ?thesis
    unfolding \<kappa>eq act_cc[OF j f lg \<open>M l\<close> \<open>M g\<close>] .
qed

end

subsection \<open>Morphisms of \<open>PSh C\<close> are the natural transformations\<close>

text \<open>
  Naturality: on the component of \<open>\<langle>j, f\<rangle>\<close> both sides give the component of \<open>\<langle>l, (g \<circ> f) \<circ> u\<rangle>\<close>.
\<close>

theorem act_natural:
  assumes "category C" and "locally_small C" and "\<phi> \<in> Arr (PSh C)"
  shows "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C (asrc \<phi>) c \<longrightarrow> act C \<phi> c \<kappa> \<in> elts C (atgt \<phi>) c"
    and "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C (asrc \<phi>) (tgt\<^bsub>C\<^esub> u) \<longrightarrow>
      act C \<phi> (src\<^bsub>C\<^esub> u) (pre C (asrc \<phi>) u \<kappa>) = pre C (atgt \<phi>) u (act C \<phi> (tgt\<^bsub>C\<^esub> u) \<kappa>)"
proof -
  note C = assms(1) and ls = assms(2)
  have \<phi>: "\<phi> \<in> PArr C"
    using assms(3) by simp
  have X: "asrc \<phi> \<in> DOb C" and Y: "atgt \<phi> \<in> DOb C"
    using \<phi> by simp_all
  show "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C (asrc \<phi>) c \<longrightarrow> act C \<phi> c \<kappa> \<in> elts C (atgt \<phi>) c"
    using act_elts[OF C ls \<phi>] by blast
  show "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C (asrc \<phi>) (tgt\<^bsub>C\<^esub> u) \<longrightarrow>
      act C \<phi> (src\<^bsub>C\<^esub> u) (pre C (asrc \<phi>) u \<kappa>) = pre C (atgt \<phi>) u (act C \<phi> (tgt\<^bsub>C\<^esub> u) \<kappa>)"
  proof (intro allI impI)
    fix u \<kappa>
    assume "M u" "M \<kappa>" and u: "u \<in> Arr C" and \<kappa>: "\<kappa> \<in> elts C (asrc \<phi>) (tgt\<^bsub>C\<^esub> u)"
    obtain j f where \<kappa>eq: "\<kappa> = cc (cgraph C (asrc \<phi>) (tgt\<^bsub>C\<^esub> u)) \<langle>j, f\<rangle>"
      and j: "j \<in> Ob (ix (asrc \<phi>))"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j"
      using \<kappa> by (rule eltsE)
    obtain l g where lg: "\<langle>l, g\<rangle> \<in> body \<phi> \<cdot> j" and "M l" and "M g" and l: "l \<in> Ob (ix (atgt \<phi>))"
      and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = dg (asrc \<phi>) \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> g = dg (atgt \<phi>) \<cdot>\<^sub>o l"
      using \<phi> j by (rule PArr_body_ex)
    have fu: "f \<circ>\<^bsub>C\<^esub> u \<in> Arr C" "src\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> u) = src\<^bsub>C\<^esub> u"
      "tgt\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> u) = dg (asrc \<phi>) \<cdot>\<^sub>o j"
      using C u f by simp_all
    have gf: "g \<circ>\<^bsub>C\<^esub> f \<in> Arr C" "src\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = tgt\<^bsub>C\<^esub> u"
      "tgt\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = dg (atgt \<phi>) \<cdot>\<^sub>o l"
      using C f g by simp_all
    have lhs: "act C \<phi> (src\<^bsub>C\<^esub> u) (pre C (asrc \<phi>) u \<kappa>) =
        cc (cgraph C (atgt \<phi>) (src\<^bsub>C\<^esub> u)) \<langle>l, g \<circ>\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> u)\<rangle>"
      unfolding \<kappa>eq pre_cc[OF C ls X u j f] using fu lg \<open>M l\<close> \<open>M g\<close>
      by (rule act_cc[OF C ls \<phi> j])
    have rhs: "pre C (atgt \<phi>) u (act C \<phi> (tgt\<^bsub>C\<^esub> u) \<kappa>) =
        cc (cgraph C (atgt \<phi>) (src\<^bsub>C\<^esub> u)) \<langle>l, (g \<circ>\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> u\<rangle>"
      unfolding \<kappa>eq act_cc[OF C ls \<phi> j f lg \<open>M l\<close> \<open>M g\<close>] using u l gf by (rule pre_cc[OF C ls Y])
    have "g \<circ>\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> u) = (g \<circ>\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> u"
      by (rule cat_assoc[OF C u f(1) g(1) f(2)]) (simp add: g(2) f(3))
    then show "act C \<phi> (src\<^bsub>C\<^esub> u) (pre C (asrc \<phi>) u \<kappa>) = pre C (atgt \<phi>) u (act C \<phi> (tgt\<^bsub>C\<^esub> u) \<kappa>)"
      unfolding lhs rhs by simp
  qed
qed

theorem act_functorial:
  assumes "category C" and "locally_small C"
  shows "\<forall>\<^sub>s X c \<kappa>. X \<in> DOb C \<longrightarrow> c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> act C (id\<^bsub>PSh C\<^esub> X) c \<kappa> = \<kappa>"
    and "\<forall>\<^sub>s \<phi> \<psi> c \<kappa>. \<phi> \<in> Arr (PSh C) \<longrightarrow> \<psi> \<in> Arr (PSh C) \<longrightarrow> src\<^bsub>PSh C\<^esub> \<psi> = tgt\<^bsub>PSh C\<^esub> \<phi> \<longrightarrow>
      c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C (asrc \<phi>) c \<longrightarrow>
      act C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) c \<kappa> = act C \<psi> c (act C \<phi> c \<kappa>)"
proof -
  note C = assms(1) and ls = assms(2)
  show "\<forall>\<^sub>s X c \<kappa>. X \<in> DOb C \<longrightarrow> c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> act C (id\<^bsub>PSh C\<^esub> X) c \<kappa> = \<kappa>"
  proof (intro allI impI)
    fix X c \<kappa>
    assume "M X" "M c" "M \<kappa>" and X: "X \<in> DOb C" and c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C X c"
    obtain j f where \<kappa>eq: "\<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>" and j: "j \<in> Ob (ix X)"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
      using \<kappa> by (rule eltsE)
    have P: "Pid C X \<in> PArr C"
      using C ls X by (rule Pid_PArr)
    have "act C (Pid C X) c (cc (cgraph C (asrc (Pid C X)) c) \<langle>j, f\<rangle>) =
        cc (cgraph C (atgt (Pid C X)) c) \<langle>j, id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule act_cc[OF C ls P]) (use C ls X j f \<open>M X\<close> in \<open>simp_all add: mem_M\<close>)
    moreover have "id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> f = f"
      using C f by simp
    ultimately show "act C (id\<^bsub>PSh C\<^esub> X) c \<kappa> = \<kappa>"
      using X \<open>M X\<close> by (simp add: \<kappa>eq)
  qed
  show "\<forall>\<^sub>s \<phi> \<psi> c \<kappa>. \<phi> \<in> Arr (PSh C) \<longrightarrow> \<psi> \<in> Arr (PSh C) \<longrightarrow> src\<^bsub>PSh C\<^esub> \<psi> = tgt\<^bsub>PSh C\<^esub> \<phi> \<longrightarrow>
      c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C (asrc \<phi>) c \<longrightarrow>
      act C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) c \<kappa> = act C \<psi> c (act C \<phi> c \<kappa>)"
  proof (intro allI impI)
    fix \<phi> \<psi> c \<kappa>
    assume "M \<phi>" "M \<psi>" "M c" "M \<kappa>" and \<phi>A: "\<phi> \<in> Arr (PSh C)" and \<psi>A: "\<psi> \<in> Arr (PSh C)"
      and st: "src\<^bsub>PSh C\<^esub> \<psi> = tgt\<^bsub>PSh C\<^esub> \<phi>" and c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C (asrc \<phi>) c"
    have \<phi>: "\<phi> \<in> PArr C" and \<psi>: "\<psi> \<in> PArr C"
      using \<phi>A \<psi>A by simp_all
    have ab: "asrc \<psi> = atgt \<phi>"
      using st \<phi> \<psi> by simp
    have "\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi> \<in> Arr (PSh C)"
      using PSh_category[OF C ls] \<phi>A \<psi>A st by (rule cat_comp)
    then have Pc: "Pcomp C \<psi> \<phi> \<in> PArr C"
      using \<phi> \<psi> by simp
    obtain j f where \<kappa>eq: "\<kappa> = cc (cgraph C (asrc \<phi>) c) \<langle>j, f\<rangle>" and j: "j \<in> Ob (ix (asrc \<phi>))"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j"
      using \<kappa> by (rule eltsE)
    obtain k h where kh: "\<langle>k, h\<rangle> \<in> body \<phi> \<cdot> j" and "M k" and "M h" and k: "k \<in> Ob (ix (atgt \<phi>))"
      and h: "h \<in> Arr C" "src\<^bsub>C\<^esub> h = dg (asrc \<phi>) \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> h = dg (atgt \<phi>) \<cdot>\<^sub>o k"
      using \<phi> j by (rule PArr_body_ex)
    have k': "k \<in> Ob (ix (asrc \<psi>))"
      using k ab by simp
    obtain l g where lg: "\<langle>l, g\<rangle> \<in> body \<psi> \<cdot> k" and "M l" and "M g"
      and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = dg (asrc \<psi>) \<cdot>\<^sub>o k"
      using \<psi> k' by (rule PArr_body_ex)
    have hf: "h \<circ>\<^bsub>C\<^esub> f \<in> Arr C" "src\<^bsub>C\<^esub> (h \<circ>\<^bsub>C\<^esub> f) = c" "tgt\<^bsub>C\<^esub> (h \<circ>\<^bsub>C\<^esub> f) = dg (asrc \<psi>) \<cdot>\<^sub>o k"
      using C f h ab by simp_all
    have lgc: "\<langle>l, g \<circ>\<^bsub>C\<^esub> h\<rangle> \<in> body (Pcomp C \<psi> \<phi>) \<cdot> j"
      unfolding mem_Pcomp_body[OF C ls \<phi> \<psi> ab j]
      using kh lg \<open>M k\<close> \<open>M h\<close> \<open>M l\<close> \<open>M g\<close> conn_refl M_opair by blast
    have lhs: "act C (Pcomp C \<psi> \<phi>) c (cc (cgraph C (asrc (Pcomp C \<psi> \<phi>)) c) \<langle>j, f\<rangle>) =
        cc (cgraph C (atgt (Pcomp C \<psi> \<phi>)) c) \<langle>l, (g \<circ>\<^bsub>C\<^esub> h) \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule act_cc[OF C ls Pc]) (use j f lgc \<open>M l\<close> in simp_all)
    have mid: "act C \<phi> c (cc (cgraph C (asrc \<phi>) c) \<langle>j, f\<rangle>) = cc (cgraph C (atgt \<phi>) c) \<langle>k, h \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule act_cc[OF C ls \<phi> j f kh \<open>M k\<close> \<open>M h\<close>])
    have rhs: "act C \<psi> c (cc (cgraph C (asrc \<psi>) c) \<langle>k, h \<circ>\<^bsub>C\<^esub> f\<rangle>) =
        cc (cgraph C (atgt \<psi>) c) \<langle>l, g \<circ>\<^bsub>C\<^esub> (h \<circ>\<^bsub>C\<^esub> f)\<rangle>"
      by (rule act_cc[OF C ls \<psi> k' hf lg \<open>M l\<close> \<open>M g\<close>])
    have assoc: "(g \<circ>\<^bsub>C\<^esub> h) \<circ>\<^bsub>C\<^esub> f = g \<circ>\<^bsub>C\<^esub> (h \<circ>\<^bsub>C\<^esub> f)"
      by (rule cat_assoc[OF C f(1) h(1) g(1), symmetric]) (simp_all add: f(3) h(2,3) g(2) ab)
    show "act C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) c \<kappa> = act C \<psi> c (act C \<phi> c \<kappa>)"
      using lhs mid rhs \<phi> \<psi> by (simp add: \<kappa>eq ab assoc)
  qed
qed

theorem act_full_and_faithful:
  assumes "category C" and "locally_small C" and "X \<in> DOb C" and "Y \<in> DOb C"
    and "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> \<in> elts C Y c"
    and "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u) \<longrightarrow>
      \<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> u, pre C X u \<kappa>\<rangle> = pre C Y u (\<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, \<kappa>\<rangle>)"
  shows "\<exists>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<and>
      (\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>) \<and>
      (\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow>
        (\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi>' c \<kappa>) \<longrightarrow> \<phi>' = \<phi>)"
proof -
  note C = assms(1) and ls = assms(2) and X = assms(3) and Y = assms(4)
  have H1: "\<eta> \<cdot> \<langle>c, \<kappa>\<rangle> \<in> elts C Y c" if "c \<in> Ob C" and "\<kappa> \<in> elts C X c" for c \<kappa>
    using assms(5) that mem_M[OF that(1)] mem_M[OF that(2)] by blast
  have H2: "\<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> u, pre C X u \<kappa>\<rangle> = pre C Y u (\<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, \<kappa>\<rangle>)"
    if "u \<in> Arr C" and "\<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u)" for u \<kappa>
    using assms(6) that mem_M[OF that(1)] mem_M[OF that(2)] by blast
  let ?F = "dg X"
  let ?e = "\<lambda>j. cc (cgraph C X (?F \<cdot>\<^sub>o j)) \<langle>j, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)\<rangle>"
  let ?t = "\<lambda>j. \<eta> \<cdot> \<langle>?F \<cdot>\<^sub>o j, ?e j\<rangle>"
  let ?\<phi> = "\<langle>\<langle>X, Y\<rangle>, \<lambda>j\<in>Ob (ix X). ?t j\<rangle>"
  have "M X" and "M Y"
    using X Y by (simp_all add: mem_M)
  have cX: "category (ix X)"
    using X by simp
  have dt: "dcls ?t"
    by dfn
  have Fj: "?F \<cdot>\<^sub>o j \<in> Ob C" if "j \<in> Ob (ix X)" for j
    using X that by simp
  have e_elts: "?e j \<in> elts C X (?F \<cdot>\<^sub>o j)" if j: "j \<in> Ob (ix X)" for j
  proof -
    have "\<langle>j, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)\<rangle> \<in> cverts C X (?F \<cdot>\<^sub>o j)"
      using C X j by (simp add: mem_M)
    then show ?thesis
      by (rule elts_ccI[OF C ls X Fj[OF j]])
  qed
  have t_elts: "?t j \<in> elts C Y (?F \<cdot>\<^sub>o j)" if j: "j \<in> Ob (ix X)" for j
    by (rule H1[OF Fj[OF j] e_elts[OF j]])
  have M\<phi>: "M (\<lambda>j\<in>Ob (ix X). ?t j)"
    using dt by simp
  have proj: "asrc ?\<phi> = X" "atgt ?\<phi> = Y"
    using \<open>M X\<close> \<open>M Y\<close> M\<phi> by simp_all
  have body_app: "body ?\<phi> \<cdot> j = ?t j" if "j \<in> Ob (ix X)" for j
    using M\<phi> dt that by simp
  text \<open>\<open>?t\<close> is compatible with the arrows of \<open>ix X\<close>: naturality of \<open>\<eta>\<close> at \<open>F u\<close>.\<close>
  have compat: "\<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<in> ?t (src\<^bsub>ix X\<^esub> u)"
    if u: "u \<in> Arr (ix X)" and "M k" and "M f" and kf: "\<langle>k, f\<rangle> \<in> ?t (tgt\<^bsub>ix X\<^esub> u)" for u k f
  proof -
    let ?s = "src\<^bsub>ix X\<^esub> u" and ?r = "tgt\<^bsub>ix X\<^esub> u"
    have st: "?s \<in> Ob (ix X)" "?r \<in> Ob (ix X)"
      using cX u by simp_all
    have Fu: "?F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?s" "tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?r"
      using X u by simp_all
    have idr: "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?r) \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?r)) = tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u)"
      "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?r)) = ?F \<cdot>\<^sub>o ?r"
      using C Fj[OF st(2)] Fu by simp_all
    have "pre C X (?F \<cdot>\<^sub>a u) (cc (cgraph C X (tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u))) \<langle>?r, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?r)\<rangle>) =
        cc (cgraph C X (src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u))) \<langle>?r, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?r) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle>"
      by (rule pre_cc[OF C ls X Fu(1) st(2) idr])
    moreover have "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?r) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u = ?F \<cdot>\<^sub>a u"
      using C Fu by simp
    ultimately have pre1: "pre C X (?F \<cdot>\<^sub>a u) (?e ?r) = cc (cgraph C X (?F \<cdot>\<^sub>o ?s)) \<langle>?r, ?F \<cdot>\<^sub>a u\<rangle>"
      using Fu by simp
    have ids: "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s) \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)) = ?F \<cdot>\<^sub>o ?s"
      "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)) = ?F \<cdot>\<^sub>o ?s"
      using C Fj[OF st(1)] by simp_all
    have "\<langle>\<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>, \<langle>?r, ?F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>\<rangle> \<in> cgraph C X (?F \<cdot>\<^sub>o ?s)"
      by (rule comma_edgesI[OF u ids])
    moreover have "?F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s) = ?F \<cdot>\<^sub>a u"
      using C Fu by simp
    ultimately have "\<langle>\<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>, \<langle>?r, ?F \<cdot>\<^sub>a u\<rangle>\<rangle> \<in> cgraph C X (?F \<cdot>\<^sub>o ?s)"
      by simp
    then have "conn (cgraph C X (?F \<cdot>\<^sub>o ?s)) \<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle> \<langle>?r, ?F \<cdot>\<^sub>a u\<rangle>"
      by (rule conn_edge[OF _ M_opair M_opair])
    then have "?e ?s = cc (cgraph C X (?F \<cdot>\<^sub>o ?s)) \<langle>?r, ?F \<cdot>\<^sub>a u\<rangle>"
      by (rule cc_eq[OF M_cgraph[OF C ls X Fj[OF st(1)]] M_opair])
    with pre1 have pre_e: "pre C X (?F \<cdot>\<^sub>a u) (?e ?r) = ?e ?s"
      by simp
    have "\<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u), pre C X (?F \<cdot>\<^sub>a u) (?e ?r)\<rangle> =
        pre C Y (?F \<cdot>\<^sub>a u) (\<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u), ?e ?r\<rangle>)"
      by (rule H2[OF Fu(1)]) (use e_elts[OF st(2)] Fu(3) in simp)
    then have ts: "?t ?s = pre C Y (?F \<cdot>\<^sub>a u) (?t ?r)"
      unfolding pre_e Fu(2,3) .
    have "\<langle>k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<in> pre C Y (?F \<cdot>\<^sub>a u) (?t ?r)"
      unfolding mem_pre using kf \<open>M k\<close> \<open>M f\<close> conn_refl M_opair by blast
    then show ?thesis
      unfolding ts .
  qed
  have comp: "\<exists>\<^sub>s v. v \<in> cverts C Y (?F \<cdot>\<^sub>o j) \<and> ?t j = cc (cgraph C Y (?F \<cdot>\<^sub>o j)) v"
    if j: "j \<in> Ob (ix X)" for j
    using t_elts[OF j] unfolding mem_elts by blast
  have \<phi>: "?\<phi> \<in> PArr C"
    by (rule PArr_LamI[OF C ls X Y dt comp compat])
  have hom: "?\<phi> \<in> Hom (PSh C) X Y"
    using \<phi> proj by simp
  text \<open>\<open>\<eta>\<close> is the action of \<open>?\<phi>\<close>: naturality of \<open>\<eta>\<close> at \<open>f\<close>, applied to \<open>[j, id]\<close>.\<close>
  have rep: "\<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C ?\<phi> c \<kappa>" if c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C X c" for c \<kappa>
  proof -
    obtain j f where \<kappa>eq: "\<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>" and j: "j \<in> Ob (ix X)"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = ?F \<cdot>\<^sub>o j"
      using \<kappa> by (rule eltsE)
    have idj: "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j) \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)) = tgt\<^bsub>C\<^esub> f"
      "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)) = ?F \<cdot>\<^sub>o j"
      using C Fj[OF j] f by simp_all
    have "pre C X f (cc (cgraph C X (tgt\<^bsub>C\<^esub> f)) \<langle>j, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)\<rangle>) =
        cc (cgraph C X (src\<^bsub>C\<^esub> f)) \<langle>j, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule pre_cc[OF C ls X f(1) j idj])
    moreover have "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> f = f"
      using C f by simp
    ultimately have pre_e: "pre C X f (?e j) = \<kappa>"
      using f by (simp add: \<kappa>eq)
    have "\<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> f, pre C X f (?e j)\<rangle> = pre C Y f (\<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> f, ?e j\<rangle>)"
      by (rule H2[OF f(1)]) (use e_elts[OF j] f(3) in simp)
    then have n: "\<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = pre C Y f (?t j)"
      unfolding pre_e f(2,3) .
    obtain l g where teq: "?t j = cc (cgraph C Y (?F \<cdot>\<^sub>o j)) \<langle>l, g\<rangle>" and l: "l \<in> Ob (ix Y)"
      and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = ?F \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> g = dg Y \<cdot>\<^sub>o l"
      using t_elts[OF j] by (rule eltsE)
    have "M l" and "M g"
      using l g by (simp_all add: mem_M)
    have g': "g \<in> Arr C" "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f" "tgt\<^bsub>C\<^esub> g = dg Y \<cdot>\<^sub>o l"
      using g f by simp_all
    have "pre C Y f (cc (cgraph C Y (tgt\<^bsub>C\<^esub> f)) \<langle>l, g\<rangle>) = cc (cgraph C Y (src\<^bsub>C\<^esub> f)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule pre_cc[OF C ls Y f(1) l g'])
    then have "pre C Y f (?t j) = cc (cgraph C Y (src\<^bsub>C\<^esub> f)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
      unfolding teq f(3) .
    moreover have "act C ?\<phi> c \<kappa> = cc (cgraph C Y c) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
    proof -
      have lg: "\<langle>l, g\<rangle> \<in> body ?\<phi> \<cdot> j"
        using body_app[OF j] teq \<open>M l\<close> \<open>M g\<close> by simp
      have "act C ?\<phi> c (cc (cgraph C (asrc ?\<phi>) c) \<langle>j, f\<rangle>) = cc (cgraph C (atgt ?\<phi>) c) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
        by (rule act_cc[OF C ls \<phi> _ _ _ _ lg \<open>M l\<close> \<open>M g\<close>]) (use j f proj in simp_all)
      then show ?thesis
        using proj by (simp add: \<kappa>eq)
    qed
    ultimately show ?thesis
      using n f(2) by simp
  qed
  text \<open>Uniqueness: an arrow \<open>\<phi>'\<close> acting as \<open>\<eta>\<close> has \<open>body \<phi>' \<cdot> j = act C \<phi>' (F j) [j, id] = ?t j\<close>.\<close>
  have uniq: "\<phi>' = ?\<phi>"
    if h: "\<phi>' \<in> Hom (PSh C) X Y"
      and hr: "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi>' c \<kappa>" for \<phi>'
  proof -
    have \<phi>': "\<phi>' \<in> PArr C"
      using h by simp
    have st': "asrc \<phi>' = X" "atgt \<phi>' = Y"
      using h \<phi>' by simp_all
    show ?thesis
    proof (rule PArr_eqI[OF \<phi>' \<phi>])
      show "asrc \<phi>' = asrc ?\<phi>" and "atgt \<phi>' = atgt ?\<phi>"
        using st' proj by simp_all
      fix j
      assume j': "j \<in> Ob (ix (asrc \<phi>'))"
      then have j: "j \<in> Ob (ix X)"
        using st' by simp
      obtain l g where lg: "\<langle>l, g\<rangle> \<in> body \<phi>' \<cdot> j" and "M l" and "M g"
        and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = dg (asrc \<phi>') \<cdot>\<^sub>o j"
        using \<phi>' j' by (rule PArr_body_ex)
      have "\<eta> \<cdot> \<langle>?F \<cdot>\<^sub>o j, ?e j\<rangle> = act C \<phi>' (?F \<cdot>\<^sub>o j) (?e j)"
        using hr Fj[OF j] e_elts[OF j] mem_M[OF Fj[OF j]] mem_M[OF e_elts[OF j]] by blast
      also have "act C \<phi>' (?F \<cdot>\<^sub>o j) (?e j) =
          cc (cgraph C (atgt \<phi>') (?F \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)\<rangle>"
        using act_cc[OF C ls \<phi>' j' _ _ _ lg \<open>M l\<close> \<open>M g\<close>, of "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j)" "?F \<cdot>\<^sub>o j"]
          C Fj[OF j] st' by simp
      also have "g \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o j) = g"
        using C g st' by simp
      also have "cc (cgraph C (atgt \<phi>') (?F \<cdot>\<^sub>o j)) \<langle>l, g\<rangle> = body \<phi>' \<cdot> j"
        using PArr_body_eq_cc[OF C ls \<phi>' j' lg] st' by simp
      finally show "body \<phi>' \<cdot> j = body ?\<phi> \<cdot> j"
        using body_app[OF j] by simp
    qed
  qed
  have "M ?\<phi>"
    by simp
  moreover have "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C ?\<phi> c \<kappa>"
    using rep by blast
  moreover have "\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow>
      (\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi>' c \<kappa>) \<longrightarrow> \<phi>' = ?\<phi>"
    using uniq by blast
  ultimately show ?thesis
    using hom by blast
qed

subsection \<open>The colimit functor is the map of colimits\<close>

theorem act_colim_functor:
  assumes "category C" and "locally_small C" and "a \<in> Arr (Diag C)" and "c \<in> Ob C"
    and "j \<in> Ob (ix (asrc a))" and "f \<in> Hom C c (dg (asrc a) \<cdot>\<^sub>o j)"
  shows "act C (colim_functor C \<cdot>\<^sub>a a) c (cc (cgraph C (asrc a) c) \<langle>j, f\<rangle>) =
    cc (cgraph C (atgt a) c) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  let ?\<phi> = "colim_functor C \<cdot>\<^sub>a a"
  have a: "a \<in> DArr C"
    using assms(3) by simp
  have \<phi>: "?\<phi> \<in> PArr C"
    using assms(1,2) a by simp
  have j: "j \<in> Ob (ix (asrc ?\<phi>))"
    using a assms(5) by simp
  have f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg (asrc ?\<phi>) \<cdot>\<^sub>o j"
    using assms(6) a by simp_all
  have lg: "\<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle> \<in> body ?\<phi> \<cdot> j"
    using assms(1,2,5) a by simp
  have "act C ?\<phi> c (cc (cgraph C (asrc ?\<phi>) c) \<langle>j, f\<rangle>) =
      cc (cgraph C (atgt ?\<phi>) c) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j \<circ>\<^bsub>C\<^esub> f\<rangle>"
    by (rule act_cc[OF assms(1,2) \<phi> j f lg M_obj M_app])
  then show ?thesis
    using a by simp
qed

end
