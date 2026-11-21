section \<open>Final functors\<close>

theory Final
  imports Graph
begin

text \<open>
  What is proved about final functors: the identity functor is final, finality depends only on
  how the functor acts, reindexing a diagram along a final functor does not change the
  connected components of its comma categories, and final functors compose.
\<close>

subsection \<open>Reading the definition\<close>

lemma final_functorI:
  assumes "\<And>j. j \<in> Ob J \<Longrightarrow> \<exists>\<^sub>s v. v \<in> comma_verts J J' q j"
    and "\<And>j u v. j \<in> Ob J \<Longrightarrow> u \<in> comma_verts J J' q j \<Longrightarrow> v \<in> comma_verts J J' q j \<Longrightarrow>
      conn (comma_edges J J' q j) u v"
  shows "final_functor q J' J"
  unfolding final_functor_def using assms by blast

lemma final_functor_obtain:
  assumes "final_functor q J' J" and "j \<in> Ob J"
  obtains a u where "a \<in> Ob J'" and "u \<in> Arr J" and "src\<^bsub>J\<^esub> u = j" and "tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o a"
proof -
  obtain v where "v \<in> comma_verts J J' q j"
    using assms unfolding final_functor_def by (blast dest: mem_M)
  then obtain a u where "v = \<langle>a, u\<rangle>" "a \<in> Ob J'" "u \<in> Arr J" "src\<^bsub>J\<^esub> u = j" "tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o a"
    by (rule comma_vertsE)
  then show ?thesis
    by (intro that)
qed

lemma final_functor_conn:
  "final_functor q J' J \<Longrightarrow> j \<in> Ob J \<Longrightarrow> u \<in> comma_verts J J' q j \<Longrightarrow> v \<in> comma_verts J J' q j \<Longrightarrow>
    conn (comma_edges J J' q j) u v"
  unfolding final_functor_def by (blast dest: mem_M)

subsection \<open>The identity functor is final\<close>

text \<open>Every vertex \<open>\<langle>k, f\<rangle>\<close> of \<open>(j \<down> id)\<close> is joined to \<open>\<langle>j, id j\<rangle>\<close> by the edge \<open>f\<close>.\<close>

lemma final_idf:
  assumes "category J"
  shows "final_functor (idf J) J J"
proof (rule final_functorI)
  fix j
  assume j: "j \<in> Ob J"
  have "\<langle>j, id\<^bsub>J\<^esub> j\<rangle> \<in> comma_verts J J (idf J) j"
    using assms j by (simp add: mem_M)
  then show "\<exists>\<^sub>s v. v \<in> comma_verts J J (idf J) j"
    using M_opair by blast
next
  fix j u v
  assume j: "j \<in> Ob J" and u: "u \<in> comma_verts J J (idf J) j" and v: "v \<in> comma_verts J J (idf J) j"
  have hub: "\<langle>\<langle>j, id\<^bsub>J\<^esub> j\<rangle>, w\<rangle> \<in> comma_edges J J (idf J) j" if "w \<in> comma_verts J J (idf J) j" for w
  proof -
    from that obtain k f where w: "w = \<langle>k, f\<rangle>" and k: "k \<in> Ob J" and f: "f \<in> Arr J"
      "src\<^bsub>J\<^esub> f = j" "tgt\<^bsub>J\<^esub> f = idf J \<cdot>\<^sub>o k"
      by (rule comma_vertsE)
    have "\<langle>\<langle>src\<^bsub>J\<^esub> f, id\<^bsub>J\<^esub> j\<rangle>, \<langle>tgt\<^bsub>J\<^esub> f, idf J \<cdot>\<^sub>a f \<circ>\<^bsub>J\<^esub> id\<^bsub>J\<^esub> j\<rangle>\<rangle> \<in> comma_edges J J (idf J) j"
      by (rule comma_edgesI) (use assms j f in simp_all)
    moreover have "idf J \<cdot>\<^sub>a f \<circ>\<^bsub>J\<^esub> id\<^bsub>J\<^esub> j = f"
      using assms f cat_id_right[OF assms f(1)] by simp
    ultimately show ?thesis
      using w k f by simp
  qed
  have "conn (comma_edges J J (idf J) j) u \<langle>j, id\<^bsub>J\<^esub> j\<rangle>"
    using hub[OF u] by (simp add: conn_edge_rev mem_M[OF u])
  also have "conn (comma_edges J J (idf J) j) \<langle>j, id\<^bsub>J\<^esub> j\<rangle> v"
    using hub[OF v] by (simp add: conn_edge mem_M[OF v])
  finally show "conn (comma_edges J J (idf J) j) u v" .
qed

subsection \<open>Finality depends only on how the functor acts\<close>

text \<open>\<open>category J'\<close> is needed because the edges of \<open>(j \<down> q)\<close> read \<open>q\<close> at sources of arrows.\<close>

lemma final_functor_agree:
  assumes "category J'" and "agree J' q q'"
  shows "final_functor q J' J \<longleftrightarrow> final_functor q' J' J"
  by (simp only: final_functor_def comma_verts_agree[OF assms(2)] comma_edges_agree[OF assms])

subsection \<open>Reindexing along a final functor\<close>

text \<open>
  For \<open>q : J' \<rightarrow> J\<close> final and \<open>F : J \<rightarrow> C\<close>, the comma graphs \<open>(x \<down> F)\<close> and \<open>(x \<down> F \<circ> q)\<close> have the
  same components, in this sense: every vertex of \<open>(x \<down> F)\<close> is connected to one of the form
  \<open>\<langle>q a, f\<rangle>\<close>, and \<open>\<langle>q a, f\<rangle>\<close>, \<open>\<langle>q b, g\<rangle>\<close> are connected in \<open>(x \<down> F)\<close> exactly when \<open>\<langle>a, f\<rangle>\<close>, \<open>\<langle>b, g\<rangle>\<close>
  are connected in \<open>(x \<down> F \<circ> q)\<close>. Here \<open>F \<circ> q\<close> is \<open>fcomp J' F q\<close> or any functor that agrees with it.
\<close>

text \<open>A vertex \<open>\<langle>j, f\<rangle>\<close> is joined to \<open>\<langle>q a, F u \<circ> f\<rangle>\<close> by the edge \<open>u : j \<rightarrow> q a\<close>.\<close>

lemma reindex_conn_vert:
  assumes "u \<in> Arr J" and "src\<^bsub>J\<^esub> u = j" and "tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o a"
    and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = x" and "tgt\<^bsub>C\<^esub> f = F \<cdot>\<^sub>o j"
  shows "conn (comma_edges C J F x) \<langle>j, f\<rangle> \<langle>q \<cdot>\<^sub>o a, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle>"
    and "conn (comma_edges C J F x) \<langle>q \<cdot>\<^sub>o a, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>j, f\<rangle>"
proof -
  have "\<langle>\<langle>src\<^bsub>J\<^esub> u, f\<rangle>, \<langle>tgt\<^bsub>J\<^esub> u, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle> \<in> comma_edges C J F x"
    by (rule comma_edgesI) (use assms in simp_all)
  then have e: "\<langle>\<langle>j, f\<rangle>, \<langle>q \<cdot>\<^sub>o a, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle> \<in> comma_edges C J F x"
    using assms by simp
  show "conn (comma_edges C J F x) \<langle>j, f\<rangle> \<langle>q \<cdot>\<^sub>o a, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle>"
    using e by (simp add: conn_edge)
  show "conn (comma_edges C J F x) \<langle>q \<cdot>\<^sub>o a, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>j, f\<rangle>"
    using e by (simp add: conn_edge_rev)
qed

text \<open>
  For a vertex \<open>\<langle>j, f\<rangle>\<close> of \<open>(x \<down> F)\<close>, the pairs \<open>\<langle>a, F u \<circ> f\<rangle>\<close> with \<open>\<langle>a, u\<rangle>\<close> a vertex of \<open>(j \<down> q)\<close> all lie
  in one component of \<open>(x \<down> F \<circ> q)\<close>: \<open>(j \<down> q)\<close> is connected, and \<open>\<langle>a, u\<rangle> \<mapsto> \<langle>a, F u \<circ> f\<rangle>\<close> maps its
  edges to edges. Here \<open>j\<close> is \<open>src u\<close>.
\<close>

lemma reindex_conn_fibre:
  assumes "M J'" and "locally_small J" and "category J'" and "category J" and "category C"
    and q: "is_functor q J' J" and qf: "final_functor q J' J" and F: "is_functor F J C"
    and a: "a \<in> Ob J'" and u: "u \<in> Arr J" "tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o a"
    and b: "b \<in> Ob J'" and w: "w \<in> Arr J" "src\<^bsub>J\<^esub> w = src\<^bsub>J\<^esub> u" "tgt\<^bsub>J\<^esub> w = q \<cdot>\<^sub>o b"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = F \<cdot>\<^sub>o src\<^bsub>J\<^esub> u"
  shows "conn (comma_edges C J' (fcomp J' F q) x) \<langle>a, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>b, F \<cdot>\<^sub>a w \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  let ?j = "src\<^bsub>J\<^esub> u"
  let ?E = "comma_edges J J' q ?j"
  let ?E' = "comma_edges C J' (fcomp J' F q) x"
  let ?h = "\<lambda>v. \<langle>pfst v, F \<cdot>\<^sub>a psnd v \<circ>\<^bsub>C\<^esub> f\<rangle>"
  have j: "?j \<in> Ob J"
    using \<open>category J\<close> u by simp
  have cq: "conn ?E \<langle>a, u\<rangle> \<langle>b, w\<rangle>"
    by (rule final_functor_conn[OF qf j]) (use a u b w in \<open>simp_all add: mem_M\<close>)
  have "conn ?E' (?h \<langle>a, u\<rangle>) (?h \<langle>b, w\<rangle>)"
  proof (rule conn_map[OF M_comma_edges[OF \<open>M J'\<close> \<open>locally_small J\<close> j \<open>category J'\<close> \<open>category J\<close> q]
        _ _ _ cq])
    show "M \<langle>a, u\<rangle>"
      by simp
    show "dfun ?h"
      by dfn
    fix c d
    assume cd: "M c" "M d" "\<langle>c, d\<rangle> \<in> ?E"
    from cd(3,1,2) obtain v e where c: "c = \<langle>src\<^bsub>J'\<^esub> e, v\<rangle>" and d: "d = \<langle>tgt\<^bsub>J'\<^esub> e, q \<cdot>\<^sub>a e \<circ>\<^bsub>J\<^esub> v\<rangle>"
      and e: "e \<in> Arr J'" and v: "v \<in> Arr J" "src\<^bsub>J\<^esub> v = ?j" "tgt\<^bsub>J\<^esub> v = q \<cdot>\<^sub>o src\<^bsub>J'\<^esub> e"
      by (rule comma_edge_pairE)
    have qe: "q \<cdot>\<^sub>a e \<in> Arr J" "src\<^bsub>J\<^esub> (q \<cdot>\<^sub>a e) = tgt\<^bsub>J\<^esub> v"
      using q e v by simp_all
    have Fv: "F \<cdot>\<^sub>a v \<in> Arr C" "src\<^bsub>C\<^esub> (F \<cdot>\<^sub>a v) = tgt\<^bsub>C\<^esub> f"
      using F v f by simp_all
    have Fqe: "F \<cdot>\<^sub>a (q \<cdot>\<^sub>a e) \<in> Arr C" "src\<^bsub>C\<^esub> (F \<cdot>\<^sub>a (q \<cdot>\<^sub>a e)) = tgt\<^bsub>C\<^esub> (F \<cdot>\<^sub>a v)"
      using F qe v by simp_all
    have "F \<cdot>\<^sub>a (q \<cdot>\<^sub>a e \<circ>\<^bsub>J\<^esub> v) \<circ>\<^bsub>C\<^esub> f = (F \<cdot>\<^sub>a (q \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> F \<cdot>\<^sub>a v) \<circ>\<^bsub>C\<^esub> f"
      using functor_comp[OF F v(1) qe] by simp
    also have "\<dots> = F \<cdot>\<^sub>a (q \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> (F \<cdot>\<^sub>a v \<circ>\<^bsub>C\<^esub> f)"
      using cat_assoc[OF \<open>category C\<close> f(1) Fv(1) Fqe(1) Fv(2) Fqe(2)] by simp
    finally have eq: "F \<cdot>\<^sub>a (q \<cdot>\<^sub>a e \<circ>\<^bsub>J\<^esub> v) \<circ>\<^bsub>C\<^esub> f = F \<cdot>\<^sub>a (q \<cdot>\<^sub>a e) \<circ>\<^bsub>C\<^esub> (F \<cdot>\<^sub>a v \<circ>\<^bsub>C\<^esub> f)" .
    have Fvf: "F \<cdot>\<^sub>a v \<circ>\<^bsub>C\<^esub> f \<in> Arr C" "src\<^bsub>C\<^esub> (F \<cdot>\<^sub>a v \<circ>\<^bsub>C\<^esub> f) = x"
      "tgt\<^bsub>C\<^esub> (F \<cdot>\<^sub>a v \<circ>\<^bsub>C\<^esub> f) = fcomp J' F q \<cdot>\<^sub>o src\<^bsub>J'\<^esub> e"
      using \<open>category C\<close> \<open>category J'\<close> F e v f Fv by simp_all
    have "\<langle>?h c, ?h d\<rangle> \<in> ?E'"
      unfolding c d using comma_edgesI[OF e Fvf] e eq v(1) by (simp add: mem_M)
    then show "conn ?E' (?h c) (?h d) \<and> conn ?E' (?h d) (?h c)"
      by (simp add: conn_edge conn_edge_rev)
  qed
  then show ?thesis
    using a u b w by (simp add: mem_M)
qed

text \<open>
  Connected in \<open>(x \<down> F)\<close> implies connected in \<open>(x \<down> F \<circ> q)\<close>. Write \<open>T \<langle>j, f\<rangle>\<close> for the class of all
  \<open>\<langle>c, F u \<circ> f\<rangle>\<close> with \<open>\<langle>c, u\<rangle>\<close> a vertex of \<open>(j \<down> q)\<close>. The property "every member of \<open>T v\<close> is
  connected to \<open>\<langle>a, f\<rangle>\<close>" holds at \<open>\<langle>q a, f\<rangle>\<close>, and along an edge \<open>v \<rightarrow> v'\<close> it holds at \<open>v\<close> exactly when it
  holds at \<open>v'\<close>, because \<open>T v' \<subseteq> T v\<close>, \<open>T v'\<close> is nonempty and \<open>T v\<close> lies in one component. So it
  holds at \<open>\<langle>q b, g\<rangle>\<close>, and \<open>\<langle>b, g\<rangle> \<in> T \<langle>q b, g\<rangle>\<close>.
\<close>

lemma reindex_conn_reflect:
  assumes "M J'" and "M J" and "category J'" and "category J" and "locally_small C" and "category C"
    and q: "is_functor q J' J" and qf: "final_functor q J' J" and F: "is_functor F J C"
    and F': "agree J' F' (fcomp J' F q)" and x: "x \<in> Ob C"
    and a: "a \<in> Ob J'" and b: "b \<in> Ob J'"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = F \<cdot>\<^sub>o (q \<cdot>\<^sub>o a)" and "M g"
    and conn_qq: "conn (comma_edges C J F x) \<langle>q \<cdot>\<^sub>o a, f\<rangle> \<langle>q \<cdot>\<^sub>o b, g\<rangle>"
  shows "conn (comma_edges C J' F' x) \<langle>a, f\<rangle> \<langle>b, g\<rangle>"
proof -
  let ?EF = "comma_edges C J F x"
  let ?E' = "comma_edges C J' (fcomp J' F q) x"
  let ?P = "\<lambda>v. \<forall>\<^sub>s c u. c \<in> Ob J' \<and> u \<in> Arr J \<and> src\<^bsub>J\<^esub> u = pfst v \<and> tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o c \<longrightarrow>
    conn ?E' \<langle>a, f\<rangle> \<langle>c, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> psnd v\<rangle>"
  have lsJ: "locally_small J"
    using \<open>M J\<close> by (rule graph_locally_small)
  note T = reindex_conn_fibre[OF \<open>M J'\<close> lsJ \<open>category J'\<close> \<open>category J\<close> \<open>category C\<close> q qf F]
  have qa: "q \<cdot>\<^sub>o a \<in> Ob J" and qb: "q \<cdot>\<^sub>o b \<in> Ob J"
    using q a b by simp_all
  have "?P \<langle>q \<cdot>\<^sub>o b, g\<rangle>"
  proof (rule conn_induct[OF M_comma_edges[OF \<open>M J\<close> \<open>locally_small C\<close> x \<open>category J\<close> \<open>category C\<close> F]
        _ conn_qq])
    show "M \<langle>q \<cdot>\<^sub>o a, f\<rangle>"
      by simp
    show "dfn ?P"
      by dfn
    show "?P \<langle>q \<cdot>\<^sub>o a, f\<rangle>"
    proof (intro allI impI)
      fix c u
      assume "M c" "M u"
        and cu: "c \<in> Ob J' \<and> u \<in> Arr J \<and> src\<^bsub>J\<^esub> u = pfst \<langle>q \<cdot>\<^sub>o a, f\<rangle> \<and> tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o c"
      have "conn ?E' \<langle>a, F \<cdot>\<^sub>a id\<^bsub>J\<^esub> (q \<cdot>\<^sub>o a) \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>c, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> f\<rangle>"
        by (rule T) (use \<open>category J\<close> a qa cu f in \<open>simp_all add: mem_M[OF f(1)]\<close>)
      moreover have "F \<cdot>\<^sub>a id\<^bsub>J\<^esub> (q \<cdot>\<^sub>o a) \<circ>\<^bsub>C\<^esub> f = f"
        using F qa f cat_id_left[OF \<open>category C\<close> f(1)] by simp
      ultimately show "conn ?E' \<langle>a, f\<rangle> \<langle>c, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> psnd \<langle>q \<cdot>\<^sub>o a, f\<rangle>\<rangle>"
        using f(1) by (simp add: mem_M)
    qed
  next
    fix v w
    assume vw: "M v" "M w" "\<langle>v, w\<rangle> \<in> ?EF" "conn ?EF \<langle>q \<cdot>\<^sub>o a, f\<rangle> v"
    from vw(3,1,2) obtain h e where v: "v = \<langle>src\<^bsub>J\<^esub> e, h\<rangle>" and w: "w = \<langle>tgt\<^bsub>J\<^esub> e, F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h\<rangle>"
      and e: "e \<in> Arr J" and h: "h \<in> Arr C" "src\<^bsub>C\<^esub> h = x" "tgt\<^bsub>C\<^esub> h = F \<cdot>\<^sub>o src\<^bsub>J\<^esub> e"
      by (rule comma_edge_pairE)
    have v_simps: "pfst v = src\<^bsub>J\<^esub> e" "psnd v = h" and w_simps: "pfst w = tgt\<^bsub>J\<^esub> e"
      "psnd w = F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h"
      unfolding v w using h(1) by (simp_all add: mem_M)
    have Fe: "F \<cdot>\<^sub>a e \<in> Arr C" "src\<^bsub>C\<^esub> (F \<cdot>\<^sub>a e) = tgt\<^bsub>C\<^esub> h"
      using F e h by simp_all
    have comp: "u \<circ>\<^bsub>J\<^esub> e \<in> Arr J" "src\<^bsub>J\<^esub> (u \<circ>\<^bsub>J\<^esub> e) = src\<^bsub>J\<^esub> e" "tgt\<^bsub>J\<^esub> (u \<circ>\<^bsub>J\<^esub> e) = tgt\<^bsub>J\<^esub> u"
      and Fcomp: "F \<cdot>\<^sub>a (u \<circ>\<^bsub>J\<^esub> e) \<circ>\<^bsub>C\<^esub> h = F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> (F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h)"
      if u: "u \<in> Arr J" "src\<^bsub>J\<^esub> u = tgt\<^bsub>J\<^esub> e" for u
    proof -
      show "u \<circ>\<^bsub>J\<^esub> e \<in> Arr J" "src\<^bsub>J\<^esub> (u \<circ>\<^bsub>J\<^esub> e) = src\<^bsub>J\<^esub> e" "tgt\<^bsub>J\<^esub> (u \<circ>\<^bsub>J\<^esub> e) = tgt\<^bsub>J\<^esub> u"
        using \<open>category J\<close> e u by simp_all
      have Fu: "F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (F \<cdot>\<^sub>a u) = tgt\<^bsub>C\<^esub> (F \<cdot>\<^sub>a e)"
        using F e u by simp_all
      have "F \<cdot>\<^sub>a (u \<circ>\<^bsub>J\<^esub> e) = F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> F \<cdot>\<^sub>a e"
        using F e u by (rule functor_comp)
      then show "F \<cdot>\<^sub>a (u \<circ>\<^bsub>J\<^esub> e) \<circ>\<^bsub>C\<^esub> h = F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> (F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h)"
        using cat_assoc[OF \<open>category C\<close> h(1) Fe(1) Fu(1) Fe(2) Fu(2)] by simp
    qed
    show "?P v \<longleftrightarrow> ?P w"
    proof
      assume Pv: "?P v"
      show "?P w"
      proof (intro allI impI)
        fix c u
        assume "M c" "M u"
          and cu: "c \<in> Ob J' \<and> u \<in> Arr J \<and> src\<^bsub>J\<^esub> u = pfst w \<and> tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o c"
        then have u: "u \<in> Arr J" "src\<^bsub>J\<^esub> u = tgt\<^bsub>J\<^esub> e"
          by (simp_all add: w_simps)
        have "conn ?E' \<langle>a, f\<rangle> \<langle>c, F \<cdot>\<^sub>a (u \<circ>\<^bsub>J\<^esub> e) \<circ>\<^bsub>C\<^esub> h\<rangle>"
          using Pv comp[OF u] cu \<open>M c\<close> v_simps by (simp add: mem_M)
        then show "conn ?E' \<langle>a, f\<rangle> \<langle>c, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> psnd w\<rangle>"
          by (simp add: Fcomp[OF u] w_simps)
      qed
    next
      assume Pw: "?P w"
      show "?P v"
      proof (intro allI impI)
        fix c u
        assume "M c" "M u"
          and cu: "c \<in> Ob J' \<and> u \<in> Arr J \<and> src\<^bsub>J\<^esub> u = pfst v \<and> tgt\<^bsub>J\<^esub> u = q \<cdot>\<^sub>o c"
        have te: "tgt\<^bsub>J\<^esub> e \<in> Ob J"
          using \<open>category J\<close> e by simp
        obtain c1 u1 where c1: "c1 \<in> Ob J'" and u1: "u1 \<in> Arr J" "src\<^bsub>J\<^esub> u1 = tgt\<^bsub>J\<^esub> e"
          "tgt\<^bsub>J\<^esub> u1 = q \<cdot>\<^sub>o c1"
          using qf te by (rule final_functor_obtain)
        have "conn ?E' \<langle>a, f\<rangle> \<langle>c1, F \<cdot>\<^sub>a u1 \<circ>\<^bsub>C\<^esub> (F \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h)\<rangle>"
          using Pw c1 u1 w_simps by (simp add: mem_M)
        then have "conn ?E' \<langle>a, f\<rangle> \<langle>c1, F \<cdot>\<^sub>a (u1 \<circ>\<^bsub>J\<^esub> e) \<circ>\<^bsub>C\<^esub> h\<rangle>"
          by (simp add: Fcomp[OF u1(1,2)])
        also have "conn ?E' \<langle>c1, F \<cdot>\<^sub>a (u1 \<circ>\<^bsub>J\<^esub> e) \<circ>\<^bsub>C\<^esub> h\<rangle> \<langle>c, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> h\<rangle>"
          by (rule T) (use c1 u1 comp[OF u1(1,2)] cu h v_simps in simp_all)
        finally show "conn ?E' \<langle>a, f\<rangle> \<langle>c, F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> psnd v\<rangle>"
          by (simp add: v_simps)
      qed
    qed
  qed
  moreover have "\<langle>q \<cdot>\<^sub>o b, g\<rangle> \<in> comma_verts C J F x"
  proof (rule comma_conn_verts[OF \<open>M J\<close> \<open>locally_small C\<close> x \<open>category J\<close> \<open>category C\<close> F _ conn_qq])
    show "\<langle>q \<cdot>\<^sub>o a, f\<rangle> \<in> comma_verts C J F x"
      using qa f by (simp add: mem_M)
  qed
  then have g: "g \<in> Arr C" "tgt\<^bsub>C\<^esub> g = F \<cdot>\<^sub>o (q \<cdot>\<^sub>o b)"
    using \<open>M g\<close> by simp_all
  ultimately have "conn ?E' \<langle>a, f\<rangle> \<langle>b, F \<cdot>\<^sub>a id\<^bsub>J\<^esub> (q \<cdot>\<^sub>o b) \<circ>\<^bsub>C\<^esub> g\<rangle>"
    using \<open>category J\<close> b qb \<open>M g\<close> by (simp add: mem_M)
  moreover have "F \<cdot>\<^sub>a id\<^bsub>J\<^esub> (q \<cdot>\<^sub>o b) \<circ>\<^bsub>C\<^esub> g = g"
    using F qb g cat_id_left[OF \<open>category C\<close> g(1)] by simp
  moreover have "comma_edges C J' F' x = ?E'"
    using \<open>category J'\<close> F' by (rule comma_edges_agree)
  ultimately show ?thesis
    by simp
qed

text \<open>Connected in \<open>(x \<down> F \<circ> q)\<close> implies connected in \<open>(x \<down> F)\<close>: \<open>\<langle>a, f\<rangle> \<mapsto> \<langle>q a, f\<rangle>\<close> maps edges to edges.\<close>

lemma reindex_conn_preserve:
  assumes "M J'" and "locally_small C" and "x \<in> Ob C" and "category J'" and "category C"
    and q: "is_functor q J' J" and F: "is_functor F J C" and F': "agree J' F' (fcomp J' F q)"
    and "M a" and "M f" and "M b" and "M g"
    and c: "conn (comma_edges C J' F' x) \<langle>a, f\<rangle> \<langle>b, g\<rangle>"
  shows "conn (comma_edges C J F x) \<langle>q \<cdot>\<^sub>o a, f\<rangle> \<langle>q \<cdot>\<^sub>o b, g\<rangle>"
proof -
  let ?E' = "comma_edges C J' (fcomp J' F q) x"
  let ?h = "\<lambda>w. \<langle>q \<cdot>\<^sub>o pfst w, psnd w\<rangle>"
  have Fq: "is_functor (fcomp J' F q) J' C"
    using \<open>category J'\<close> q F by (rule graph_fcomp_functor)
  have c': "conn ?E' \<langle>a, f\<rangle> \<langle>b, g\<rangle>"
    using c comma_edges_agree[OF \<open>category J'\<close> F'] by simp
  have "conn (comma_edges C J F x) (?h \<langle>a, f\<rangle>) (?h \<langle>b, g\<rangle>)"
  proof (rule conn_map[OF M_comma_edges[OF \<open>M J'\<close> \<open>locally_small C\<close> \<open>x \<in> Ob C\<close> \<open>category J'\<close>
        \<open>category C\<close> Fq] _ _ _ c'])
    show "M \<langle>a, f\<rangle>"
      by simp
    show "dfun ?h"
      by dfn
    fix v w
    assume vw: "M v" "M w" "\<langle>v, w\<rangle> \<in> ?E'"
    from vw(3,1,2) obtain h e where v: "v = \<langle>src\<^bsub>J'\<^esub> e, h\<rangle>"
      and w: "w = \<langle>tgt\<^bsub>J'\<^esub> e, fcomp J' F q \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h\<rangle>" and e: "e \<in> Arr J'"
      and h: "h \<in> Arr C" "src\<^bsub>C\<^esub> h = x" "tgt\<^bsub>C\<^esub> h = fcomp J' F q \<cdot>\<^sub>o src\<^bsub>J'\<^esub> e"
      by (rule comma_edge_pairE)
    have qe: "q \<cdot>\<^sub>a e \<in> Arr J" "src\<^bsub>J\<^esub> (q \<cdot>\<^sub>a e) = q \<cdot>\<^sub>o src\<^bsub>J'\<^esub> e" "tgt\<^bsub>J\<^esub> (q \<cdot>\<^sub>a e) = q \<cdot>\<^sub>o tgt\<^bsub>J'\<^esub> e"
      using q e by simp_all
    have h': "tgt\<^bsub>C\<^esub> h = F \<cdot>\<^sub>o src\<^bsub>J\<^esub> (q \<cdot>\<^sub>a e)"
      using h(3) qe \<open>category J'\<close> e by simp
    have "\<langle>?h v, ?h w\<rangle> \<in> comma_edges C J F x"
      unfolding v w using comma_edgesI[OF qe(1) h(1,2) h'] qe e h(1) by (simp add: mem_M)
    then show "conn (comma_edges C J F x) (?h v) (?h w) \<and> conn (comma_edges C J F x) (?h w) (?h v)"
      by (simp add: conn_edge conn_edge_rev)
  qed
  then show ?thesis
    using assms by simp
qed

lemma reindex_conn_iff:
  assumes "M J'" and "M J" and "category J'" and "category J" and "locally_small C" and "category C"
    and q: "is_functor q J' J" and qf: "final_functor q J' J" and F: "is_functor F J C"
    and F': "agree J' F' (fcomp J' F q)" and x: "x \<in> Ob C"
    and a: "a \<in> Ob J'" and b: "b \<in> Ob J'"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = F \<cdot>\<^sub>o (q \<cdot>\<^sub>o a)" and "M g"
  shows "conn (comma_edges C J F x) \<langle>q \<cdot>\<^sub>o a, f\<rangle> \<langle>q \<cdot>\<^sub>o b, g\<rangle> \<longleftrightarrow> conn (comma_edges C J' F' x) \<langle>a, f\<rangle> \<langle>b, g\<rangle>"
proof
  assume "conn (comma_edges C J F x) \<langle>q \<cdot>\<^sub>o a, f\<rangle> \<langle>q \<cdot>\<^sub>o b, g\<rangle>"
  then show "conn (comma_edges C J' F' x) \<langle>a, f\<rangle> \<langle>b, g\<rangle>"
    by (rule reindex_conn_reflect[OF assms])
next
  assume c: "conn (comma_edges C J' F' x) \<langle>a, f\<rangle> \<langle>b, g\<rangle>"
  show "conn (comma_edges C J F x) \<langle>q \<cdot>\<^sub>o a, f\<rangle> \<langle>q \<cdot>\<^sub>o b, g\<rangle>"
    by (rule reindex_conn_preserve[OF \<open>M J'\<close> \<open>locally_small C\<close> x \<open>category J'\<close> \<open>category C\<close> q F F'
          _ _ _ _ c])
      (use a b f \<open>M g\<close> in \<open>simp_all add: mem_M\<close>)
qed

subsection \<open>Final functors compose\<close>

text \<open>
  A vertex of \<open>(j \<down> r \<circ> q)\<close> is a vertex \<open>\<langle>q c, f\<rangle>\<close> of \<open>(j \<down> r)\<close>; two of them are connected in \<open>(j \<down> r)\<close>
  because \<open>r\<close> is final, hence in \<open>(j \<down> r \<circ> q)\<close> by reindexing along \<open>q\<close>, with \<open>C = J\<close> and \<open>F = r\<close>.
\<close>

lemma final_functor_fcomp:
  assumes "M J''" and "M J'" and "locally_small J" and "category J''" and "category J'"
    and "category J" and q: "is_functor q J'' J'" and r: "is_functor r J' J"
    and qf: "final_functor q J'' J'" and rf: "final_functor r J' J"
  shows "final_functor (fcomp J'' r q) J'' J"
proof (rule final_functorI)
  fix j
  assume j: "j \<in> Ob J"
  obtain a u where a: "a \<in> Ob J'" and u: "u \<in> Arr J" "src\<^bsub>J\<^esub> u = j" "tgt\<^bsub>J\<^esub> u = r \<cdot>\<^sub>o a"
    using rf j by (rule final_functor_obtain)
  obtain c w where c: "c \<in> Ob J''" and w: "w \<in> Arr J'" "src\<^bsub>J'\<^esub> w = a" "tgt\<^bsub>J'\<^esub> w = q \<cdot>\<^sub>o c"
    using qf a by (rule final_functor_obtain)
  have "\<langle>c, r \<cdot>\<^sub>a w \<circ>\<^bsub>J\<^esub> u\<rangle> \<in> comma_verts J J'' (fcomp J'' r q) j"
    using \<open>category J\<close> r c w u by (simp add: mem_M)
  then show "\<exists>\<^sub>s v. v \<in> comma_verts J J'' (fcomp J'' r q) j"
    using M_opair by blast
next
  fix j v v'
  assume j: "j \<in> Ob J" and v: "v \<in> comma_verts J J'' (fcomp J'' r q) j"
    and v': "v' \<in> comma_verts J J'' (fcomp J'' r q) j"
  obtain c f where vcf: "v = \<langle>c, f\<rangle>" and c: "c \<in> Ob J''" and f: "f \<in> Arr J" "src\<^bsub>J\<^esub> f = j"
    "tgt\<^bsub>J\<^esub> f = fcomp J'' r q \<cdot>\<^sub>o c"
    using v by (rule comma_vertsE)
  obtain d g where vdg: "v' = \<langle>d, g\<rangle>" and d: "d \<in> Ob J''" and g: "g \<in> Arr J" "src\<^bsub>J\<^esub> g = j"
    "tgt\<^bsub>J\<^esub> g = fcomp J'' r q \<cdot>\<^sub>o d"
    using v' by (rule comma_vertsE)
  have cr: "conn (comma_edges J J' r j) \<langle>q \<cdot>\<^sub>o c, f\<rangle> \<langle>q \<cdot>\<^sub>o d, g\<rangle>"
    by (rule final_functor_conn[OF rf j]) (use q c d f g in \<open>simp_all add: mem_M\<close>)
  have "conn (comma_edges J J'' (fcomp J'' r q) j) \<langle>c, f\<rangle> \<langle>d, g\<rangle>"
    by (rule reindex_conn_reflect[OF \<open>M J''\<close> \<open>M J'\<close> \<open>category J''\<close> \<open>category J'\<close> \<open>locally_small J\<close>
          \<open>category J\<close> q qf r graph_agree_refl j c d _ _ _ _ cr])
      (use c f g in \<open>simp_all add: mem_M\<close>)
  then show "conn (comma_edges J J'' (fcomp J'' r q) j) v v'"
    by (simp only: vcf vdg)
qed

end
