section \<open>Connected components, comma categories and final functors\<close>

theory Graph
  imports Category
begin

subsection \<open>Connectedness without natural numbers\<close>

text \<open>
  A graph is given by its class \<open>E\<close> of edges, a class of ordered pairs. Two vertices are
  connected when every set that is closed under the edges, in both directions, and contains
  the first contains the second. For a small graph this is the equivalence relation generated
  by the edges, and \<open>cc E u\<close>, the smallest closed set containing \<open>u\<close>, is the connected component
  of \<open>u\<close>. No zigzags, so no natural numbers and no axiom of infinity.

  The quantifier over \<open>S\<close> ranges over sets, so the definition is only right when the component
  of \<open>u\<close> is a set, in particular when \<open>E\<close> is a set. All graphs below are small.
\<close>

definition eclosed :: "cls \<Rightarrow> cls \<Rightarrow> bool"
  where "eclosed E S \<longleftrightarrow> (\<forall>\<^sub>s u v. \<langle>u, v\<rangle> \<in> E \<longrightarrow> (u \<in> S \<longleftrightarrow> v \<in> S))"

definition conn :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "conn E u v \<longleftrightarrow> (\<forall>\<^sub>s S. eclosed E S \<longrightarrow> u \<in> S \<longrightarrow> v \<in> S)"

definition cc :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "cc E u = \<lbrace>v. conn E u v\<rbrace>"

subsection \<open>The comma category of an object over a functor\<close>

text \<open>
  For a functor \<open>G : K \<rightarrow> C\<close> and an object \<open>x\<close> of \<open>C\<close>, the comma category \<open>(x \<down> G)\<close> has objects
  the pairs \<open>\<langle>k, f\<rangle>\<close> with \<open>f : x \<rightarrow> G k\<close>, and an arrow \<open>\<langle>k, f\<rangle> \<rightarrow> \<langle>k', G b \<circ> f\<rangle>\<close> for each \<open>b : k \<rightarrow> k'\<close>.
  Only its underlying graph is needed: \<open>comma_verts C K G x\<close> and \<open>comma_edges C K G x\<close>.
  Its set of connected components is \<open>colim\<^sub>k Hom(x, G k)\<close>.
\<close>

definition comma_verts :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "comma_verts C K G x =
    \<lbrace>v. \<exists>\<^sub>s k f. v = \<langle>k, f\<rangle> \<and> k \<in> Ob K \<and> f \<in> Arr C \<and> src\<^bsub>C\<^esub> f = x \<and> tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o k\<rbrace>"

definition comma_edges :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "comma_edges C K G x =
    \<lbrace>e. \<exists>\<^sub>s f b. e = \<langle>\<langle>src\<^bsub>K\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle> \<and>
      b \<in> Arr K \<and> f \<in> Arr C \<and> src\<^bsub>C\<^esub> f = x \<and> tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b\<rbrace>"

subsection \<open>Final functors\<close>

text \<open>
  A functor \<open>q : J' \<rightarrow> J\<close> is final when \<open>(j \<down> q)\<close> is nonempty and connected for every object \<open>j\<close>
  of \<open>J\<close>.
\<close>

definition final_functor :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "final_functor q J' J \<longleftrightarrow>
    (\<forall>\<^sub>s j. j \<in> Ob J \<longrightarrow>
      (\<exists>\<^sub>s v. v \<in> comma_verts J J' q j) \<and>
      (\<forall>\<^sub>s u v. u \<in> comma_verts J J' q j \<longrightarrow> v \<in> comma_verts J J' q j \<longrightarrow>
        conn (comma_edges J J' q j) u v))"

subsection \<open>Class existence for this vocabulary\<close>

lemma dfn_eclosed [dfn_rules]: "dcls E \<Longrightarrow> dcls S \<Longrightarrow> dfn (\<lambda>x. eclosed (E x) (S x))"
  unfolding eclosed_def by dfn

lemma dfn_conn [dfn_rules]: "dcls E \<Longrightarrow> dfun u \<Longrightarrow> dfun v \<Longrightarrow> dfn (\<lambda>x. conn (E x) (u x) (v x))"
  unfolding conn_def by dfn

lemma dcls_cc [dfn_rules]: "dcls E \<Longrightarrow> dfun u \<Longrightarrow> dcls (\<lambda>x. cc (E x) (u x))"
  unfolding cc_def by dfn

lemma dcls_comma_verts [dfn_rules]:
  "dcls C \<Longrightarrow> dcls K \<Longrightarrow> dcls G \<Longrightarrow> dcls A \<Longrightarrow> dcls (\<lambda>x. comma_verts (C x) (K x) (G x) (A x))"
  unfolding comma_verts_def by dfn

lemma dcls_comma_edges [dfn_rules]:
  "dcls C \<Longrightarrow> dcls K \<Longrightarrow> dcls G \<Longrightarrow> dcls A \<Longrightarrow> dcls (\<lambda>x. comma_edges (C x) (K x) (G x) (A x))"
  unfolding comma_edges_def by dfn

lemma dfn_final_functor [dfn_rules]:
  "dcls Q \<Longrightarrow> dcls J' \<Longrightarrow> dcls J \<Longrightarrow> dfn (\<lambda>x. final_functor (Q x) (J' x) (J x))"
  unfolding final_functor_def by dfn

subsection \<open>Connectedness: the basic rules\<close>

text \<open>
  Reflexivity, transitivity and single edges need no smallness. Symmetry needs a closed set
  containing the first vertex: if there is none, \<open>conn E u v\<close> holds for every \<open>v\<close>. For a small
  graph the endpoints of the edges together with \<open>u\<close> form such a set.
\<close>

lemma eclosedI:
  "(\<And>a b. M a \<Longrightarrow> M b \<Longrightarrow> \<langle>a, b\<rangle> \<in> E \<Longrightarrow> a \<in> S \<longleftrightarrow> b \<in> S) \<Longrightarrow> eclosed E S"
  unfolding eclosed_def by blast

lemma eclosedD: "eclosed E S \<Longrightarrow> \<langle>a, b\<rangle> \<in> E \<Longrightarrow> M a \<Longrightarrow> M b \<Longrightarrow> a \<in> S \<longleftrightarrow> b \<in> S"
  unfolding eclosed_def by blast

lemma connI: "(\<And>S. M S \<Longrightarrow> eclosed E S \<Longrightarrow> u \<in> S \<Longrightarrow> v \<in> S) \<Longrightarrow> conn E u v"
  unfolding conn_def by blast

lemma connD: "conn E u v \<Longrightarrow> M S \<Longrightarrow> eclosed E S \<Longrightarrow> u \<in> S \<Longrightarrow> v \<in> S"
  unfolding conn_def by blast

lemma conn_refl [simp]: "conn E u u"
  by (rule connI)

lemma conn_trans [trans]: "conn E u v \<Longrightarrow> conn E v w \<Longrightarrow> conn E u w"
  unfolding conn_def by blast

lemma conn_edge: "\<langle>u, v\<rangle> \<in> E \<Longrightarrow> M u \<Longrightarrow> M v \<Longrightarrow> conn E u v"
  by (rule connI) (blast dest: eclosedD)

lemma conn_edge_rev: "\<langle>u, v\<rangle> \<in> E \<Longrightarrow> M u \<Longrightarrow> M v \<Longrightarrow> conn E v u"
  by (rule connI) (blast dest: eclosedD)

lemma conn_mono: "conn E u v \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> conn E' u v"
  unfolding conn_def eclosed_def by blast

lemma conn_sym_closed:
  assumes uv: "conn E u v" and "M S0" and "eclosed E S0" and "u \<in> S0"
  shows "conn E v u"
proof (rule connI)
  fix S
  assume "M S" and S: "eclosed E S" and "v \<in> S"
  show "u \<in> S"
  proof (rule ccontr)
    assume "u \<notin> S"
    have "M (S0 \<setminus> S)"
      using \<open>M S0\<close> by simp
    moreover have "eclosed E (S0 \<setminus> S)"
    proof (rule eclosedI)
      fix a b
      assume "M a" "M b" "\<langle>a, b\<rangle> \<in> E"
      then show "a \<in> S0 \<setminus> S \<longleftrightarrow> b \<in> S0 \<setminus> S"
        using eclosedD[OF \<open>eclosed E S0\<close>] eclosedD[OF S] by simp
    qed
    moreover have "u \<in> S0 \<setminus> S"
      using \<open>u \<in> S0\<close> \<open>u \<notin> S\<close> by simp
    ultimately have "v \<in> S0 \<setminus> S"
      using uv by (rule connD[rotated])
    with \<open>v \<in> S\<close> show False
      by simp
  qed
qed

text \<open>The endpoints of the edges together with \<open>u\<close>: a closed class, a set when \<open>E\<close> is.\<close>

lemma eclosed_field: "eclosed E (cdom E \<union> cran E \<union> sng u)"
  by (rule eclosedI) auto

lemma M_field: "M E \<Longrightarrow> M (cdom E \<union> cran E \<union> sng u)"
  by simp

lemma mem_field: "M u \<Longrightarrow> u \<in> cdom E \<union> cran E \<union> sng u"
  by simp

lemma conn_sym: "M E \<Longrightarrow> M u \<Longrightarrow> conn E u v \<Longrightarrow> conn E v u"
  by (rule conn_sym_closed[OF _ M_field eclosed_field mem_field])

lemma conn_sym_iff: "M E \<Longrightarrow> M u \<Longrightarrow> M v \<Longrightarrow> conn E u v \<longleftrightarrow> conn E v u"
  using conn_sym by blast

lemma conn_M: "M E \<Longrightarrow> M u \<Longrightarrow> conn E u v \<Longrightarrow> M v"
  using connD[OF _ M_field eclosed_field mem_field] by (blast intro: mem_M)

subsection \<open>Connected components\<close>

text \<open>
  \<open>cc E u\<close> is the class of the vertices connected to \<open>u\<close>. It is closed under the edges, and a set
  containing \<open>u\<close> when \<open>E\<close> and \<open>u\<close> are sets; two vertices have the same component exactly when they
  are connected.
\<close>

lemma dfn_conn_right: "dfn (\<lambda>v. conn E u v)"
proof (cases "M u")
  case True
  then show ?thesis
    by dfn
next
  case False
  then have "conn E u v" for v
    unfolding conn_def by (blast dest: mem_M)
  then show ?thesis
    by (intro dfn_cong[OF dfn_const[of True]]) simp
qed

lemma mem_cc [simp]: "v \<in> cc E u \<longleftrightarrow> M v \<and> conn E u v"
  unfolding cc_def by (rule Coll_iff[OF dfn_conn_right])

lemma cc_self: "M u \<Longrightarrow> u \<in> cc E u"
  by simp

lemma cc_closed: "eclosed E (cc E u)"
proof (rule eclosedI)
  fix a b
  assume "M a" "M b" "\<langle>a, b\<rangle> \<in> E"
  then have "conn E a b" and "conn E b a"
    by (simp_all add: conn_edge conn_edge_rev)
  with \<open>M a\<close> \<open>M b\<close> show "a \<in> cc E u \<longleftrightarrow> b \<in> cc E u"
    by (auto intro: conn_trans)
qed

lemma M_cc: "M E \<Longrightarrow> M u \<Longrightarrow> M (cc E u)"
proof -
  assume "M E" "M u"
  have "cc E u \<subseteq> cdom E \<union> cran E \<union> sng u"
  proof
    fix v
    assume "v \<in> cc E u"
    then have "conn E u v"
      by simp
    then show "v \<in> cdom E \<union> cran E \<union> sng u"
      by (rule connD[OF _ M_field[OF \<open>M E\<close>] eclosed_field mem_field[OF \<open>M u\<close>]])
  qed
  with M_field[OF \<open>M E\<close>] show ?thesis
    by (rule M_subcls)
qed

lemma cc_eq: "M E \<Longrightarrow> M u \<Longrightarrow> conn E u v \<Longrightarrow> cc E u = cc E v"
  by (rule cls_eqI) (auto intro: conn_trans conn_sym)

lemma cc_eq_iff: "M E \<Longrightarrow> M u \<Longrightarrow> M v \<Longrightarrow> cc E u = cc E v \<longleftrightarrow> conn E u v"
proof
  assume "M E" "M u" "M v" "cc E u = cc E v"
  then have "v \<in> cc E u"
    by simp
  then show "conn E u v"
    by simp
qed (rule cc_eq)

text \<open>
  Induction along a component: a definable property that is invariant along the edges inside
  the component of \<open>u\<close> passes from \<open>u\<close> to every vertex connected to it. The set of members of
  \<open>cc E u\<close> with the property is closed.
\<close>

lemma conn_induct:
  assumes "M E" and "M u" and uv: "conn E u v" and "dfn P" and "P u"
    and step: "\<And>a b. M a \<Longrightarrow> M b \<Longrightarrow> \<langle>a, b\<rangle> \<in> E \<Longrightarrow> conn E u a \<Longrightarrow> P a \<longleftrightarrow> P b"
  shows "P v"
proof -
  let ?S = "\<lbrace>x. x \<in> cc E u \<and> P x\<rbrace>"
  have mem_S: "x \<in> ?S \<longleftrightarrow> M x \<and> conn E u x \<and> P x" for x
    using \<open>dfn P\<close> dfun_const[OF \<open>M u\<close>] by simp
  have "M ?S"
    using M_cc[OF \<open>M E\<close> \<open>M u\<close>] \<open>dfn P\<close> by (rule M_sep)
  moreover have "eclosed E ?S"
  proof (rule eclosedI)
    fix a b
    assume ab: "M a" "M b" "\<langle>a, b\<rangle> \<in> E"
    have ab': "conn E a b" "conn E b a"
      using ab by (simp_all add: conn_edge conn_edge_rev)
    show "a \<in> ?S \<longleftrightarrow> b \<in> ?S"
    proof
      assume "a \<in> ?S"
      then show "b \<in> ?S"
        using step[OF ab] ab ab' unfolding mem_S by (blast intro: conn_trans)
    next
      assume "b \<in> ?S"
      then have "conn E u a"
        using ab' unfolding mem_S by (blast intro: conn_trans)
      with \<open>b \<in> ?S\<close> show "a \<in> ?S"
        using step[OF ab] ab unfolding mem_S by blast
    qed
  qed
  moreover have "u \<in> ?S"
    using \<open>M u\<close> \<open>P u\<close> unfolding mem_S by simp
  ultimately have "v \<in> ?S"
    using uv by (rule connD[rotated])
  then show ?thesis
    unfolding mem_S by blast
qed

text \<open>
  Maps of graphs. A definable operation that sends every edge of a small graph to a pair of
  vertices connected both ways (or one way, when the target graph is small too) sends
  connected vertices to connected vertices. Smallness of the source graph is needed: in a
  proper class graph in which no set containing \<open>u\<close> is closed, \<open>u\<close> is connected to everything.
\<close>

lemma conn_map:
  assumes "M E" and "M u" and "dfun h"
    and edge: "\<And>a b. M a \<Longrightarrow> M b \<Longrightarrow> \<langle>a, b\<rangle> \<in> E \<Longrightarrow> conn E' (h a) (h b) \<and> conn E' (h b) (h a)"
    and uv: "conn E u v"
  shows "conn E' (h u) (h v)"
proof (rule connI)
  fix S'
  assume "M S'" and S': "eclosed E' S'" and "h u \<in> S'"
  let ?S = "\<lbrace>x. x \<in> cc E u \<and> h x \<in> S'\<rbrace>"
  have mem_S: "x \<in> ?S \<longleftrightarrow> M x \<and> conn E u x \<and> h x \<in> S'" for x
    using \<open>dfun h\<close> dfun_const[OF \<open>M u\<close>] by simp
  have "M ?S"
    using M_cc[OF \<open>M E\<close> \<open>M u\<close>] by (rule M_sep) (use \<open>dfun h\<close> in dfn)
  moreover have "eclosed E ?S"
  proof (rule eclosedI)
    fix a b
    assume ab: "M a" "M b" "\<langle>a, b\<rangle> \<in> E"
    have "a \<in> cc E u \<longleftrightarrow> b \<in> cc E u"
      using eclosedD[OF cc_closed ab(3) ab(1,2)] .
    moreover have "h a \<in> S' \<longleftrightarrow> h b \<in> S'"
      using edge[OF ab] connD[OF _ \<open>M S'\<close> S'] by blast
    ultimately show "a \<in> ?S \<longleftrightarrow> b \<in> ?S"
      using ab unfolding mem_S by simp
  qed
  moreover have "u \<in> ?S"
    using \<open>M u\<close> \<open>h u \<in> S'\<close> unfolding mem_S by simp
  ultimately have "v \<in> ?S"
    using uv by (rule connD[rotated])
  then show "h v \<in> S'"
    unfolding mem_S by blast
qed

lemma conn_map_small:
  assumes "M E" and "M u" and "M E'" and "dfun h"
    and edge: "\<And>a b. M a \<Longrightarrow> M b \<Longrightarrow> \<langle>a, b\<rangle> \<in> E \<Longrightarrow> conn E' (h a) (h b)"
    and uv: "conn E u v"
  shows "conn E' (h u) (h v)"
proof (rule conn_map[OF assms(1,2,4) _ uv])
  fix a b
  assume ab: "M a" "M b" "\<langle>a, b\<rangle> \<in> E"
  have "M (h a)"
    using \<open>dfun h\<close> \<open>M a\<close> by (rule dfun_M)
  with edge[OF ab] \<open>M E'\<close> show "conn E' (h a) (h b) \<and> conn E' (h b) (h a)"
    by (blast intro: conn_sym)
qed

subsection \<open>Facts about categories and functors used here\<close>

text \<open>
  General facts that are not in \<open>Category\<close>: a small category is locally small, functors that
  agree, and the composite of two functors is a functor.
\<close>

lemma graph_M_Ob: "M C \<Longrightarrow> M (Ob C)"
  by (simp add: Ob_def)

lemma graph_M_Arr: "M C \<Longrightarrow> M (Arr C)"
  by (simp add: Arr_def)

lemma graph_Hom_subcls: "Hom C x y \<subseteq> Arr C"
  by auto

lemma graph_locally_smallD: "locally_small C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> y \<in> Ob C \<Longrightarrow> M (Hom C x y)"
  unfolding locally_small_def by (blast dest: mem_M)

lemma graph_locally_small: "M C \<Longrightarrow> locally_small C"
  unfolding locally_small_def using M_subcls[OF graph_M_Arr graph_Hom_subcls] by blast

lemma graph_agree_refl [simp]: "agree C F F"
  unfolding agree_def by blast

lemma graph_agree_sym: "agree C F G \<Longrightarrow> agree C G F"
  unfolding agree_def by simp

lemma graph_agree_obj: "agree C F G \<Longrightarrow> x \<in> Ob C \<Longrightarrow> F \<cdot>\<^sub>o x = G \<cdot>\<^sub>o x"
  unfolding agree_def by (blast dest: mem_M)

lemma graph_agree_arr: "agree C F G \<Longrightarrow> f \<in> Arr C \<Longrightarrow> F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f"
  unfolding agree_def by (blast dest: mem_M)

lemma graph_fcomp_functor:
  assumes "category C" and F: "is_functor F C D" and G: "is_functor G D E"
  shows "is_functor (fcomp C G F) C E"
proof (rule is_functorI)
  fix f g
  assume fg: "f \<in> Arr C" "g \<in> Arr C" "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f"
  have "F \<cdot>\<^sub>a (g \<circ>\<^bsub>C\<^esub> f) = F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f"
    using F fg by (rule functor_comp)
  moreover have "G \<cdot>\<^sub>a (F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f) = G \<cdot>\<^sub>a (F \<cdot>\<^sub>a g) \<circ>\<^bsub>E\<^esub> G \<cdot>\<^sub>a (F \<cdot>\<^sub>a f)"
    using G by (rule functor_comp) (use F fg in simp_all)
  ultimately show "fcomp C G F \<cdot>\<^sub>a (g \<circ>\<^bsub>C\<^esub> f) = fcomp C G F \<cdot>\<^sub>a g \<circ>\<^bsub>E\<^esub> fcomp C G F \<cdot>\<^sub>a f"
    using \<open>category C\<close> fg by simp
qed (use assms in simp_all)

subsection \<open>Comma graphs: vertices and edges\<close>

text \<open>
  Reading the vertices and the edges of \<open>(x \<down> G)\<close>. A pair is only a pair of sets, so the rules
  for a given pair \<open>\<langle>k, f\<rangle>\<close> ask that \<open>k\<close> and \<open>f\<close> be sets.
\<close>

lemma mem_comma_verts [simp]:
  "M k \<Longrightarrow> M f \<Longrightarrow> \<langle>k, f\<rangle> \<in> comma_verts C K G x \<longleftrightarrow>
    k \<in> Ob K \<and> f \<in> Arr C \<and> src\<^bsub>C\<^esub> f = x \<and> tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o k"
  unfolding comma_verts_def by auto

lemma comma_vertsE:
  assumes "v \<in> comma_verts C K G x"
  obtains k f where "v = \<langle>k, f\<rangle>" and "k \<in> Ob K" and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = x"
    and "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o k"
  using assms unfolding comma_verts_def by auto

lemma comma_edgesI:
  assumes "b \<in> Arr K" and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = x" and "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
  shows "\<langle>\<langle>src\<^bsub>K\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle> \<in> comma_edges C K G x"
  unfolding comma_edges_def using assms mem_M[OF assms(1)] mem_M[OF assms(2)] by auto

lemma comma_edgesE:
  assumes "e \<in> comma_edges C K G x"
  obtains f b where "e = \<langle>\<langle>src\<^bsub>K\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle>" and "b \<in> Arr K"
    and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = x" and "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
  using assms unfolding comma_edges_def by auto

lemma comma_edge_pairE:
  assumes "\<langle>v, w\<rangle> \<in> comma_edges C K G x" and "M v" and "M w"
  obtains f b where "v = \<langle>src\<^bsub>K\<^esub> b, f\<rangle>" and "w = \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>" and "b \<in> Arr K"
    and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = x" and "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
proof -
  obtain f b where e: "\<langle>v, w\<rangle> = \<langle>\<langle>src\<^bsub>K\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle>"
    and rest: "b \<in> Arr K" "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
    using assms(1) by (rule comma_edgesE)
  from e assms(2,3) have vw: "v = \<langle>src\<^bsub>K\<^esub> b, f\<rangle>" "w = \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>"
    by simp_all
  show ?thesis
    by (rule that[OF vw rest])
qed

text \<open>Both endpoints of an edge are vertices, so the class of vertices is closed.\<close>

lemma comma_edge_verts:
  assumes "category K" and "category C" and G: "is_functor G K C"
    and "\<langle>v, w\<rangle> \<in> comma_edges C K G x" and "M v" and "M w"
  shows "v \<in> comma_verts C K G x" and "w \<in> comma_verts C K G x"
proof -
  obtain f b where v: "v = \<langle>src\<^bsub>K\<^esub> b, f\<rangle>" and w: "w = \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>"
    and b: "b \<in> Arr K" and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
    using assms(4-6) by (rule comma_edge_pairE)
  show "v \<in> comma_verts C K G x"
    unfolding v using assms(1) b f by (simp add: mem_M)
  show "w \<in> comma_verts C K G x"
    unfolding w using assms(1,2) G b f by (simp add: mem_M)
qed

lemma comma_verts_closed:
  assumes "category K" and "category C" and "is_functor G K C"
  shows "eclosed (comma_edges C K G x) (comma_verts C K G x)"
proof (rule eclosedI)
  fix a b
  assume "M a" "M b" "\<langle>a, b\<rangle> \<in> comma_edges C K G x"
  then have "a \<in> comma_verts C K G x" and "b \<in> comma_verts C K G x"
    using comma_edge_verts[OF assms] by blast+
  then show "a \<in> comma_verts C K G x \<longleftrightarrow> b \<in> comma_verts C K G x"
    by blast
qed

subsection \<open>Comma graphs are small\<close>

text \<open>
  Over a small \<open>K\<close> and a locally small \<open>C\<close>, the vertices of \<open>(x \<down> G)\<close> lie in the union of the sets
  \<open>{k} \<times> Hom(x, G k)\<close>, and the edges are pairs of vertices. So the graph is small, its components
  are sets, and the component of a vertex consists of vertices.
\<close>

lemma M_comma_verts:
  assumes "M K" and "locally_small C" and "x \<in> Ob C" and G: "is_functor G K C"
  shows "M (comma_verts C K G x)"
proof -
  let ?U = "\<lbrace>y. \<exists>\<^sub>s k. k \<in> Ob K \<and> y \<in> sng k \<times> Hom C x (G \<cdot>\<^sub>o k)\<rbrace>"
  have "M ?U"
  proof (rule M_UN)
    show "M (Ob K)"
      using \<open>M K\<close> by (rule graph_M_Ob)
    show "dcls (\<lambda>k. sng k \<times> Hom C x (G \<cdot>\<^sub>o k))"
      by dfn
    fix k
    assume "k \<in> Ob K"
    then show "M (sng k \<times> Hom C x (G \<cdot>\<^sub>o k))"
      using assms by (simp add: graph_locally_smallD)
  qed
  moreover have "comma_verts C K G x \<subseteq> ?U"
  proof
    fix v
    assume "v \<in> comma_verts C K G x"
    then obtain k f where "v = \<langle>k, f\<rangle>" "k \<in> Ob K" "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x"
      "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o k"
      by (rule comma_vertsE)
    then show "v \<in> ?U"
      by (auto simp: mem_M)
  qed
  ultimately show ?thesis
    by (rule M_subcls)
qed

lemma M_comma_edges:
  assumes "M K" and "locally_small C" and "x \<in> Ob C" and "category K" and "category C"
    and G: "is_functor G K C"
  shows "M (comma_edges C K G x)"
proof -
  have "comma_edges C K G x \<subseteq> comma_verts C K G x \<times> comma_verts C K G x"
  proof
    fix e
    assume e_in: "e \<in> comma_edges C K G x"
    then obtain f b where e: "e = \<langle>\<langle>src\<^bsub>K\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle>"
      by (rule comma_edgesE)
    with e_in have e_in': "\<langle>\<langle>src\<^bsub>K\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle> \<in> comma_edges C K G x"
      by simp
    show "e \<in> comma_verts C K G x \<times> comma_verts C K G x"
      unfolding e using comma_edge_verts[OF assms(4-6) e_in'] by simp
  qed
  moreover have "M (comma_verts C K G x \<times> comma_verts C K G x)"
    using M_comma_verts[OF assms(1-3) G] by simp
  ultimately show ?thesis
    by (rule M_subcls[rotated])
qed

lemma M_comma_cc:
  "M K \<Longrightarrow> locally_small C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> category K \<Longrightarrow> category C \<Longrightarrow> is_functor G K C \<Longrightarrow>
    M v \<Longrightarrow> M (cc (comma_edges C K G x) v)"
  by (rule M_cc[OF M_comma_edges])

lemma comma_conn_verts:
  assumes "M K" and "locally_small C" and "x \<in> Ob C" and "category K" and "category C"
    and "is_functor G K C"
    and "v \<in> comma_verts C K G x" and "conn (comma_edges C K G x) v w"
  shows "w \<in> comma_verts C K G x"
  using assms(8) M_comma_verts[OF assms(1-3,6)] comma_verts_closed[OF assms(4-6)] assms(7)
  by (rule connD)

lemma comma_cc_verts:
  assumes "M K" and "locally_small C" and "x \<in> Ob C" and "category K" and "category C"
    and "is_functor G K C" and "v \<in> comma_verts C K G x"
  shows "cc (comma_edges C K G x) v \<subseteq> comma_verts C K G x"
  using comma_conn_verts[OF assms(1-7)] by auto

subsection \<open>Comma graphs depend only on how the functor acts\<close>

text \<open>
  The edges need \<open>category K\<close>: an edge reads \<open>G\<close> at \<open>src b\<close>, and \<open>agree\<close> says nothing about \<open>G\<close>
  off the objects of \<open>K\<close>.
\<close>

lemma comma_verts_agree_subcls:
  assumes "agree K G G'"
  shows "comma_verts C K G x \<subseteq> comma_verts C K G' x"
proof
  fix v
  assume "v \<in> comma_verts C K G x"
  then obtain k f where v: "v = \<langle>k, f\<rangle>" and k: "k \<in> Ob K" and f: "f \<in> Arr C"
    "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o k"
    by (rule comma_vertsE)
  have "G \<cdot>\<^sub>o k = G' \<cdot>\<^sub>o k"
    using assms k by (rule graph_agree_obj)
  then show "v \<in> comma_verts C K G' x"
    unfolding v using k f by (simp add: mem_M)
qed

lemma comma_verts_agree: "agree K G G' \<Longrightarrow> comma_verts C K G x = comma_verts C K G' x"
  by (rule subcls_antisym) (simp_all add: comma_verts_agree_subcls graph_agree_sym)

lemma comma_edges_agree_subcls:
  assumes "category K" and "agree K G G'"
  shows "comma_edges C K G x \<subseteq> comma_edges C K G' x"
proof
  fix e
  assume "e \<in> comma_edges C K G x"
  then obtain f b where e: "e = \<langle>\<langle>src\<^bsub>K\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>K\<^esub> b, G \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle>"
    and b: "b \<in> Arr K" and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = x" "tgt\<^bsub>C\<^esub> f = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
    by (rule comma_edgesE)
  have eqs: "G \<cdot>\<^sub>a b = G' \<cdot>\<^sub>a b" "G \<cdot>\<^sub>o src\<^bsub>K\<^esub> b = G' \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
    using assms b by (simp_all add: graph_agree_arr graph_agree_obj)
  have "tgt\<^bsub>C\<^esub> f = G' \<cdot>\<^sub>o src\<^bsub>K\<^esub> b"
    using f(3) eqs(2) by simp
  from comma_edgesI[OF b f(1,2) this] show "e \<in> comma_edges C K G' x"
    unfolding e eqs(1) .
qed

lemma comma_edges_agree:
  "category K \<Longrightarrow> agree K G G' \<Longrightarrow> comma_edges C K G x = comma_edges C K G' x"
  by (rule subcls_antisym) (simp_all add: comma_edges_agree_subcls graph_agree_sym)

subsection \<open>Maps between comma graphs\<close>

text \<open>
  Precomposition with \<open>u : x' \<rightarrow> x\<close> maps \<open>(x \<down> G)\<close> to \<open>(x' \<down> G)\<close>, and a morphism of diagrams
  \<open>(p, \<alpha>) : F \<rightarrow> G\<close> maps \<open>(x \<down> F)\<close> to \<open>(x \<down> G)\<close>, edges to edges. So both preserve connectedness.
  The naturality of \<open>\<alpha>\<close> is written as in \<open>DArr\<close>.
\<close>

lemma comma_conn_precomp:
  assumes "M K" and "locally_small C" and "category K" and "category C" and G: "is_functor G K C"
    and u: "u \<in> Arr C" "tgt\<^bsub>C\<^esub> u = x"
    and "M k" and "M f" and "M k'" and "M f'"
    and uv: "conn (comma_edges C K G x) \<langle>k, f\<rangle> \<langle>k', f'\<rangle>"
  shows "conn (comma_edges C K G (src\<^bsub>C\<^esub> u)) \<langle>k, f \<circ>\<^bsub>C\<^esub> u\<rangle> \<langle>k', f' \<circ>\<^bsub>C\<^esub> u\<rangle>"
proof -
  let ?h = "\<lambda>w. \<langle>pfst w, psnd w \<circ>\<^bsub>C\<^esub> u\<rangle>"
  have "x \<in> Ob C"
    using cat_tgt[OF \<open>category C\<close> u(1)] u(2) by simp
  have "conn (comma_edges C K G (src\<^bsub>C\<^esub> u)) (?h \<langle>k, f\<rangle>) (?h \<langle>k', f'\<rangle>)"
  proof (rule conn_map[OF M_comma_edges[OF \<open>M K\<close> \<open>locally_small C\<close> \<open>x \<in> Ob C\<close> \<open>category K\<close>
        \<open>category C\<close> G] _ _ _ uv])
    show "M \<langle>k, f\<rangle>"
      by simp
    show "dfun ?h"
      by dfn
    fix a b
    assume ab: "M a" "M b" "\<langle>a, b\<rangle> \<in> comma_edges C K G x"
    from ab(3,1,2) obtain g c where a: "a = \<langle>src\<^bsub>K\<^esub> c, g\<rangle>" and b: "b = \<langle>tgt\<^bsub>K\<^esub> c, G \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> g\<rangle>"
      and c: "c \<in> Arr K" and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = x" "tgt\<^bsub>C\<^esub> g = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> c"
      by (rule comma_edge_pairE)
    have Gc: "G \<cdot>\<^sub>a c \<in> Arr C" "src\<^bsub>C\<^esub> (G \<cdot>\<^sub>a c) = tgt\<^bsub>C\<^esub> g"
      using G c g by simp_all
    have assoc: "(G \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> g) \<circ>\<^bsub>C\<^esub> u = G \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> u)"
      using cat_assoc[OF \<open>category C\<close> u(1) g(1) Gc(1)] g(2) u(2) Gc(2) by simp
    have gu: "g \<circ>\<^bsub>C\<^esub> u \<in> Arr C" "src\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> u) = src\<^bsub>C\<^esub> u"
      "tgt\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> u) = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> c"
      using \<open>category C\<close> u g by simp_all
    have "\<langle>?h a, ?h b\<rangle> \<in> comma_edges C K G (src\<^bsub>C\<^esub> u)"
      unfolding a b using comma_edgesI[OF c gu] assoc g(1) by (simp add: mem_M)
    then show "conn (comma_edges C K G (src\<^bsub>C\<^esub> u)) (?h a) (?h b) \<and>
        conn (comma_edges C K G (src\<^bsub>C\<^esub> u)) (?h b) (?h a)"
      by (simp add: conn_edge conn_edge_rev)
  qed
  then show ?thesis
    using assms by simp
qed

lemma comma_conn_morphism:
  assumes "M J" and "locally_small C" and "x \<in> Ob C" and "category J" and "category C"
    and F: "is_functor F J C" and G: "is_functor G K C" and p: "is_functor p J K"
    and \<alpha>_arr: "\<And>j. j \<in> Ob J \<Longrightarrow> \<alpha> \<cdot> j \<in> Arr C"
    and \<alpha>_src: "\<And>j. j \<in> Ob J \<Longrightarrow> src\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = F \<cdot>\<^sub>o j"
    and \<alpha>_tgt: "\<And>j. j \<in> Ob J \<Longrightarrow> tgt\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = G \<cdot>\<^sub>o (p \<cdot>\<^sub>o j)"
    and \<alpha>_nat: "\<And>u. u \<in> Arr J \<Longrightarrow>
      \<alpha> \<cdot> tgt\<^bsub>J\<^esub> u \<circ>\<^bsub>C\<^esub> F \<cdot>\<^sub>a u = G \<cdot>\<^sub>a (p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> \<alpha> \<cdot> src\<^bsub>J\<^esub> u"
    and "M j" and "M f" and "M j'" and "M f'"
    and uv: "conn (comma_edges C J F x) \<langle>j, f\<rangle> \<langle>j', f'\<rangle>"
  shows "conn (comma_edges C K G x) \<langle>p \<cdot>\<^sub>o j, \<alpha> \<cdot> j \<circ>\<^bsub>C\<^esub> f\<rangle> \<langle>p \<cdot>\<^sub>o j', \<alpha> \<cdot> j' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
proof -
  let ?h = "\<lambda>w. \<langle>p \<cdot>\<^sub>o pfst w, \<alpha> \<cdot> pfst w \<circ>\<^bsub>C\<^esub> psnd w\<rangle>"
  have "conn (comma_edges C K G x) (?h \<langle>j, f\<rangle>) (?h \<langle>j', f'\<rangle>)"
  proof (rule conn_map[OF M_comma_edges[OF \<open>M J\<close> \<open>locally_small C\<close> \<open>x \<in> Ob C\<close> \<open>category J\<close>
        \<open>category C\<close> F] _ _ _ uv])
    show "M \<langle>j, f\<rangle>"
      by simp
    show "dfun ?h"
      by dfn
    fix a b
    assume ab: "M a" "M b" "\<langle>a, b\<rangle> \<in> comma_edges C J F x"
    from ab(3,1,2) obtain g c where a: "a = \<langle>src\<^bsub>J\<^esub> c, g\<rangle>" and b: "b = \<langle>tgt\<^bsub>J\<^esub> c, F \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> g\<rangle>"
      and c: "c \<in> Arr J" and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = x" "tgt\<^bsub>C\<^esub> g = F \<cdot>\<^sub>o src\<^bsub>J\<^esub> c"
      by (rule comma_edge_pairE)
    have sc: "src\<^bsub>J\<^esub> c \<in> Ob J" and tc: "tgt\<^bsub>J\<^esub> c \<in> Ob J"
      using \<open>category J\<close> c by simp_all
    have Fc: "F \<cdot>\<^sub>a c \<in> Arr C" "src\<^bsub>C\<^esub> (F \<cdot>\<^sub>a c) = tgt\<^bsub>C\<^esub> g"
      using F c g by simp_all
    have pc: "p \<cdot>\<^sub>a c \<in> Arr K" "src\<^bsub>K\<^esub> (p \<cdot>\<^sub>a c) = p \<cdot>\<^sub>o src\<^bsub>J\<^esub> c" "tgt\<^bsub>K\<^esub> (p \<cdot>\<^sub>a c) = p \<cdot>\<^sub>o tgt\<^bsub>J\<^esub> c"
      using p c by simp_all
    have Gpc: "G \<cdot>\<^sub>a (p \<cdot>\<^sub>a c) \<in> Arr C"
      "src\<^bsub>C\<^esub> (G \<cdot>\<^sub>a (p \<cdot>\<^sub>a c)) = tgt\<^bsub>C\<^esub> (\<alpha> \<cdot> src\<^bsub>J\<^esub> c)"
      using G pc \<alpha>_tgt[OF sc] by simp_all
    have ag: "\<alpha> \<cdot> src\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> g \<in> Arr C" "src\<^bsub>C\<^esub> (\<alpha> \<cdot> src\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> g) = x"
      "tgt\<^bsub>C\<^esub> (\<alpha> \<cdot> src\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> g) = G \<cdot>\<^sub>o src\<^bsub>K\<^esub> (p \<cdot>\<^sub>a c)"
      using \<open>category C\<close> g \<alpha>_arr[OF sc] \<alpha>_src[OF sc] \<alpha>_tgt[OF sc] pc by simp_all
    have "\<alpha> \<cdot> tgt\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> (F \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> g) = (\<alpha> \<cdot> tgt\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> F \<cdot>\<^sub>a c) \<circ>\<^bsub>C\<^esub> g"
      using cat_assoc[OF \<open>category C\<close> g(1) Fc(1) \<alpha>_arr[OF tc]] Fc(2) \<alpha>_src[OF tc] F c
      by simp
    also have "\<dots> = (G \<cdot>\<^sub>a (p \<cdot>\<^sub>a c) \<circ>\<^bsub>C\<^esub> \<alpha> \<cdot> src\<^bsub>J\<^esub> c) \<circ>\<^bsub>C\<^esub> g"
      using \<alpha>_nat[OF c] by simp
    also have "\<dots> = G \<cdot>\<^sub>a (p \<cdot>\<^sub>a c) \<circ>\<^bsub>C\<^esub> (\<alpha> \<cdot> src\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> g)"
      using cat_assoc[OF \<open>category C\<close> g(1) \<alpha>_arr[OF sc] Gpc(1)] \<alpha>_src[OF sc] g(3) Gpc(2)
      by simp
    finally have nat: "\<alpha> \<cdot> tgt\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> (F \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> g) =
      G \<cdot>\<^sub>a (p \<cdot>\<^sub>a c) \<circ>\<^bsub>C\<^esub> (\<alpha> \<cdot> src\<^bsub>J\<^esub> c \<circ>\<^bsub>C\<^esub> g)" .
    have "\<langle>?h a, ?h b\<rangle> \<in> comma_edges C K G x"
      unfolding a b using comma_edgesI[OF pc(1) ag] pc nat g(1) by (simp add: mem_M)
    then show "conn (comma_edges C K G x) (?h a) (?h b) \<and> conn (comma_edges C K G x) (?h b) (?h a)"
      by (simp add: conn_edge conn_edge_rev)
  qed
  then show ?thesis
    using assms by simp
qed

end
