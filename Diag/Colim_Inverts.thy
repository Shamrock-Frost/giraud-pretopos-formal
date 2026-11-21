section \<open>The colimit functor inverts the final reindexings\<close>

theory Colim_Inverts
  imports Final_Reindexing Colim_Functor
begin

text \<open>
  A final reindexing does not change the colimit. For \<open>w : \<langle>J', F'\<rangle> \<rightarrow> \<langle>J, F\<rangle>\<close> in \<open>W0 C\<close> with
  functor part \<open>q\<close>, the image \<open>\<phi>\<close> of \<open>w\<close> has at \<open>j'\<close> the component of \<open>\<langle>q j', id\<rangle>\<close>. Its inverse
  \<open>\<psi>\<close> has at an object \<open>j\<close> of \<open>J\<close> the class of the vertices \<open>\<langle>a, f\<rangle>\<close> of \<open>(F j \<down> F')\<close> whose image
  \<open>\<langle>q a, f\<rangle>\<close> in \<open>(F j \<down> F)\<close> is connected to \<open>\<langle>j, id\<rangle>\<close>. That class is written without choosing a
  representative; finality of \<open>q\<close> makes it one component.
\<close>

subsection \<open>Two arrows whose bodies share a member\<close>

text \<open>
  Two arrows of \<open>PSh C\<close> with the same source and target agree at \<open>j\<close> as soon as their bodies at
  \<open>j\<close> have a common member, since each is the component of that member. This is a reading lemma
  of \<open>PSh_Basics\<close>.
\<close>

lemma PArr_body_share:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C" and b: "b \<in> PArr C"
    and src: "asrc a = asrc b" and tgt: "atgt a = atgt b" and j: "j \<in> Ob (ix (asrc a))"
    and va: "v \<in> body a \<cdot> j" and vb: "v \<in> body b \<cdot> j"
  shows "body a \<cdot> j = body b \<cdot> j"
proof -
  have jb: "j \<in> Ob (ix (asrc b))"
    using j src by simp
  show ?thesis
    using PArr_body_eq_cc[OF C ls a j va] PArr_body_eq_cc[OF C ls b jb vb] src tgt by simp
qed

subsection \<open>The inverse\<close>

definition W0_inv_at :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "W0_inv_at C w j =
    \<lbrace>v. v \<in> cverts C (asrc w) (dg (atgt w) \<cdot>\<^sub>o j) \<and>
      conn (cgraph C (atgt w) (dg (atgt w) \<cdot>\<^sub>o j))
        \<langle>afun w \<cdot>\<^sub>o pfst v, psnd v\<rangle> \<langle>j, id\<^bsub>C\<^esub> (dg (atgt w) \<cdot>\<^sub>o j)\<rangle>\<rbrace>"

definition W0_inv :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "W0_inv C w = \<langle>\<langle>atgt w, asrc w\<rangle>, \<lambda>j\<in>Ob (ix (atgt w)). W0_inv_at C w j\<rangle>"

lemma dcls_W0_inv_at [dfn_rules]:
  "dcls C \<Longrightarrow> dcls W \<Longrightarrow> dfun J \<Longrightarrow> dcls (\<lambda>x. W0_inv_at (C x) (W x) (J x))"
  unfolding W0_inv_at_def by dfn

text \<open>Reading the inverse: its members, that it is a set, its source, target and body.\<close>

lemma mem_W0_inv_at:
  assumes "M j" and "M a" and "M f"
  shows "\<langle>a, f\<rangle> \<in> W0_inv_at C w j \<longleftrightarrow>
    a \<in> Ob (ix (asrc w)) \<and> f \<in> Arr C \<and> src\<^bsub>C\<^esub> f = dg (atgt w) \<cdot>\<^sub>o j \<and>
    tgt\<^bsub>C\<^esub> f = dg (asrc w) \<cdot>\<^sub>o a \<and>
    conn (cgraph C (atgt w) (dg (atgt w) \<cdot>\<^sub>o j)) \<langle>afun w \<cdot>\<^sub>o a, f\<rangle> \<langle>j, id\<^bsub>C\<^esub> (dg (atgt w) \<cdot>\<^sub>o j)\<rangle>"
  unfolding W0_inv_at_def using assms by (simp add: dfun_const[OF \<open>M j\<close>])

lemma W0_inv_at_sub:
  assumes "M j"
  shows "W0_inv_at C w j \<subseteq> cverts C (asrc w) (dg (atgt w) \<cdot>\<^sub>o j)"
  unfolding W0_inv_at_def using assms by (auto simp: dfun_const[OF \<open>M j\<close>])

lemma M_W0_inv_at:
  assumes ls: "locally_small C" and w: "w \<in> DArr C" and j: "j \<in> Ob (ix (atgt w))"
  shows "M (W0_inv_at C w j)"
proof -
  have "M (cverts C (asrc w) (dg (atgt w) \<cdot>\<^sub>o j))"
    using ls w j by simp
  then show ?thesis
    using W0_inv_at_sub[OF mem_M[OF j]] by (rule M_subcls)
qed

lemma asrc_W0_inv [simp]: "asrc (W0_inv C w) = atgt w"
  by (simp add: W0_inv_def)

lemma atgt_W0_inv [simp]: "atgt (W0_inv C w) = asrc w"
  by (simp add: W0_inv_def)

lemma body_W0_inv_app:
  assumes "locally_small C" and "w \<in> DArr C" and "j \<in> Ob (ix (atgt w))"
  shows "body (W0_inv C w) \<cdot> j = W0_inv_at C w j"
  using assms M_W0_inv_at[OF assms] by (simp add: W0_inv_def)

subsection \<open>The inverse is an arrow, and it is inverse\<close>

context
  fixes C w
  assumes C: "category C" and ls: "locally_small C" and w: "w \<in> W0 C"
begin

private lemma wD: "w \<in> DArr C"
  using w by simp

private lemma X: "atgt w \<in> DOb C"
  using wD by simp

private lemma X': "asrc w \<in> DOb C"
  using wD by simp

private lemma cJ: "category (ix (atgt w))"
  using wD by simp

private lemma cJ': "category (ix (asrc w))"
  using wD by simp

private lemma FX: "is_functor (dg (atgt w)) (ix (atgt w)) C"
  using X by (rule DOb_functor)

private lemma q: "is_functor (afun w) (ix (asrc w)) (ix (atgt w))"
  using wD by (rule DArr_functor)

private lemma qf: "final_functor (afun w) (ix (asrc w)) (ix (atgt w))"
  using w by (rule W0_final)

private lemma ag: "agree (ix (asrc w)) (dg (asrc w)) (fcomp (ix (asrc w)) (dg (atgt w)) (afun w))"
  using w by (rule W0_agree)

private lemma Fq: "a \<in> Ob (ix (asrc w)) \<Longrightarrow> dg (atgt w) \<cdot>\<^sub>o (afun w \<cdot>\<^sub>o a) = dg (asrc w) \<cdot>\<^sub>o a"
  by (rule W0_dg_obj[OF w])

text \<open>An arrow \<open>u : j \<rightarrow> q a\<close> joins \<open>\<langle>j, id\<rangle>\<close> to \<open>\<langle>q a, F u\<rangle>\<close>.\<close>

private lemma hub:
  assumes j: "j \<in> Ob (ix (atgt w))" and a: "a \<in> Ob (ix (asrc w))"
    and u: "u \<in> Arr (ix (atgt w))" "src\<^bsub>ix (atgt w)\<^esub> u = j" "tgt\<^bsub>ix (atgt w)\<^esub> u = afun w \<cdot>\<^sub>o a"
  shows "conn (cgraph C (atgt w) (dg (atgt w) \<cdot>\<^sub>o j))
      \<langle>j, id\<^bsub>C\<^esub> (dg (atgt w) \<cdot>\<^sub>o j)\<rangle> \<langle>afun w \<cdot>\<^sub>o a, dg (atgt w) \<cdot>\<^sub>a u\<rangle>"
    and "conn (cgraph C (atgt w) (dg (atgt w) \<cdot>\<^sub>o j))
      \<langle>afun w \<cdot>\<^sub>o a, dg (atgt w) \<cdot>\<^sub>a u\<rangle> \<langle>j, id\<^bsub>C\<^esub> (dg (atgt w) \<cdot>\<^sub>o j)\<rangle>"
proof -
  let ?F = "dg (atgt w)"
  let ?x = "?F \<cdot>\<^sub>o j"
  have x: "?x \<in> Ob C"
    using X j by simp
  have idx: "id\<^bsub>C\<^esub> ?x \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> ?x) = ?x" "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> ?x) = ?F \<cdot>\<^sub>o j"
    using C x by simp_all
  have Fu: "?F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?x"
    using X u by simp_all
  have eq: "?F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> ?x = ?F \<cdot>\<^sub>a u"
    using C Fu by simp
  show "conn (cgraph C (atgt w) ?x) \<langle>j, id\<^bsub>C\<^esub> ?x\<rangle> \<langle>afun w \<cdot>\<^sub>o a, ?F \<cdot>\<^sub>a u\<rangle>"
    using reindex_conn_vert(1)[OF u idx] unfolding eq .
  show "conn (cgraph C (atgt w) ?x) \<langle>afun w \<cdot>\<^sub>o a, ?F \<cdot>\<^sub>a u\<rangle> \<langle>j, id\<^bsub>C\<^esub> ?x\<rangle>"
    using reindex_conn_vert(2)[OF u idx] unfolding eq .
qed

text \<open>
  For \<open>u : j \<rightarrow> q a\<close>, the inverse at \<open>j\<close> is the component of \<open>\<langle>a, F u\<rangle>\<close> in \<open>(F j \<down> F')\<close>: a vertex
  \<open>\<langle>b, g\<rangle>\<close> has \<open>\<langle>q b, g\<rangle>\<close> connected to \<open>\<langle>j, id\<rangle>\<close> exactly when \<open>\<langle>q b, g\<rangle>\<close> is connected to \<open>\<langle>q a, F u\<rangle>\<close>,
  that is, by reindexing, when \<open>\<langle>b, g\<rangle>\<close> is connected to \<open>\<langle>a, F u\<rangle>\<close>.
\<close>

lemma W0_inv_at_cc:
  assumes j: "j \<in> Ob (ix (atgt w))" and a: "a \<in> Ob (ix (asrc w))"
    and u: "u \<in> Arr (ix (atgt w))" "src\<^bsub>ix (atgt w)\<^esub> u = j" "tgt\<^bsub>ix (atgt w)\<^esub> u = afun w \<cdot>\<^sub>o a"
  shows "W0_inv_at C w j = cc (cgraph C (asrc w) (dg (atgt w) \<cdot>\<^sub>o j)) \<langle>a, dg (atgt w) \<cdot>\<^sub>a u\<rangle>"
proof (rule ext)
  let ?X = "atgt w" and ?X' = "asrc w" and ?q = "afun w"
  let ?F = "dg ?X" and ?x = "dg ?X \<cdot>\<^sub>o j"
  let ?E = "cgraph C ?X ?x" and ?E' = "cgraph C ?X' ?x"
  let ?i = "\<langle>j, id\<^bsub>C\<^esub> ?x\<rangle>"
  fix z
  have x: "?x \<in> Ob C"
    using X j by simp
  have ME: "M ?E"
    using C ls X x by simp
  have Fu: "?F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?x" "tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o (?q \<cdot>\<^sub>o a)"
    using X u by simp_all
  note h = hub[OF j a u]
  have conn_char: "conn ?E \<langle>?q \<cdot>\<^sub>o b, g\<rangle> ?i \<longleftrightarrow> conn ?E' \<langle>a, ?F \<cdot>\<^sub>a u\<rangle> \<langle>b, g\<rangle>"
    if b: "b \<in> Ob (ix ?X')" and "M g" for b g
  proof -
    have "conn ?E \<langle>?q \<cdot>\<^sub>o b, g\<rangle> ?i \<longleftrightarrow> conn ?E \<langle>?q \<cdot>\<^sub>o a, ?F \<cdot>\<^sub>a u\<rangle> \<langle>?q \<cdot>\<^sub>o b, g\<rangle>"
    proof
      assume "conn ?E \<langle>?q \<cdot>\<^sub>o b, g\<rangle> ?i"
      then have "conn ?E ?i \<langle>?q \<cdot>\<^sub>o b, g\<rangle>"
        by (rule conn_sym[OF ME M_opair])
      then show "conn ?E \<langle>?q \<cdot>\<^sub>o a, ?F \<cdot>\<^sub>a u\<rangle> \<langle>?q \<cdot>\<^sub>o b, g\<rangle>"
        by (rule conn_trans[OF h(2)])
    next
      assume "conn ?E \<langle>?q \<cdot>\<^sub>o a, ?F \<cdot>\<^sub>a u\<rangle> \<langle>?q \<cdot>\<^sub>o b, g\<rangle>"
      then have "conn ?E ?i \<langle>?q \<cdot>\<^sub>o b, g\<rangle>"
        by (rule conn_trans[OF h(1)])
      then show "conn ?E \<langle>?q \<cdot>\<^sub>o b, g\<rangle> ?i"
        by (rule conn_sym[OF ME M_opair])
    qed
    also have "\<dots> \<longleftrightarrow> conn ?E' \<langle>a, ?F \<cdot>\<^sub>a u\<rangle> \<langle>b, g\<rangle>"
      by (rule reindex_conn_iff[OF M_ix M_ix cJ' cJ ls C q qf FX ag x a b Fu(1,2,3) \<open>M g\<close>])
    finally show ?thesis .
  qed
  show "z \<in> W0_inv_at C w j \<longleftrightarrow> z \<in> cc ?E' \<langle>a, ?F \<cdot>\<^sub>a u\<rangle>"
  proof
    assume z: "z \<in> W0_inv_at C w j"
    have "z \<in> cverts C ?X' ?x"
      using W0_inv_at_sub[OF mem_M[OF j]] z by (rule subclsD)
    then obtain b g where zbg: "z = \<langle>b, g\<rangle>" and b: "b \<in> Ob (ix ?X')" and g: "g \<in> Arr C"
      "src\<^bsub>C\<^esub> g = ?x" "tgt\<^bsub>C\<^esub> g = dg ?X' \<cdot>\<^sub>o b"
      by (rule comma_vertsE)
    have zW: "\<langle>b, g\<rangle> \<in> W0_inv_at C w j"
      using z zbg by simp
    have "conn ?E \<langle>?q \<cdot>\<^sub>o b, g\<rangle> ?i"
      using mem_W0_inv_at[OF mem_M[OF j] mem_M[OF b] mem_M[OF g(1)], THEN iffD1, OF zW] by blast
    then have "conn ?E' \<langle>a, ?F \<cdot>\<^sub>a u\<rangle> \<langle>b, g\<rangle>"
      using conn_char[OF b mem_M[OF g(1)]] by simp
    then show "z \<in> cc ?E' \<langle>a, ?F \<cdot>\<^sub>a u\<rangle>"
      using zbg by simp
  next
    assume z: "z \<in> cc ?E' \<langle>a, ?F \<cdot>\<^sub>a u\<rangle>"
    then have c: "conn ?E' \<langle>a, ?F \<cdot>\<^sub>a u\<rangle> z"
      by simp
    have v0: "\<langle>a, ?F \<cdot>\<^sub>a u\<rangle> \<in> cverts C ?X' ?x"
      using a Fu Fq[OF a] by (simp add: mem_M)
    have "z \<in> cverts C ?X' ?x"
      by (rule cgraph_conn_verts[OF C ls X' x v0 c])
    then obtain b g where zbg: "z = \<langle>b, g\<rangle>" and b: "b \<in> Ob (ix ?X')" and g: "g \<in> Arr C"
      "src\<^bsub>C\<^esub> g = ?x" "tgt\<^bsub>C\<^esub> g = dg ?X' \<cdot>\<^sub>o b"
      by (rule comma_vertsE)
    have "conn ?E \<langle>?q \<cdot>\<^sub>o b, g\<rangle> ?i"
      using c conn_char[OF b mem_M[OF g(1)]] zbg by simp
    then have "\<langle>b, g\<rangle> \<in> W0_inv_at C w j"
      using b g mem_W0_inv_at[OF mem_M[OF j] mem_M[OF b] mem_M[OF g(1)]] by simp
    then show "z \<in> W0_inv_at C w j"
      using zbg by simp
  qed
qed

text \<open>
  The inverse is an arrow \<open>\<langle>J, F\<rangle> \<rightarrow> \<langle>J', F'\<rangle>\<close>. At each \<open>j\<close> it is a component, by finality and
  \<open>W0_inv_at_cc\<close>. Compatibility: for \<open>u : s \<rightarrow> t\<close> and \<open>\<langle>k, f\<rangle>\<close> at \<open>t\<close>, precomposing the connection
  \<open>\<langle>q k, f\<rangle> \<sim> \<langle>t, id\<rangle>\<close> with \<open>F u\<close> gives \<open>\<langle>q k, f \<circ> F u\<rangle> \<sim> \<langle>t, F u\<rangle>\<close>, and the edge \<open>u\<close> joins
  \<open>\<langle>s, id\<rangle>\<close> to \<open>\<langle>t, F u\<rangle>\<close>.
\<close>

lemma W0_inv_PArr: "W0_inv C w \<in> PArr C"
  unfolding W0_inv_def
proof (rule PArr_LamI[OF C ls X X'])
  show "dcls (\<lambda>j. W0_inv_at C w j)"
    by dfn
  show "\<exists>\<^sub>s v. v \<in> cverts C (asrc w) (dg (atgt w) \<cdot>\<^sub>o j) \<and>
      W0_inv_at C w j = cc (cgraph C (asrc w) (dg (atgt w) \<cdot>\<^sub>o j)) v"
    if j: "j \<in> Ob (ix (atgt w))" for j
  proof -
    obtain a u where a: "a \<in> Ob (ix (asrc w))" and u: "u \<in> Arr (ix (atgt w))"
      "src\<^bsub>ix (atgt w)\<^esub> u = j" "tgt\<^bsub>ix (atgt w)\<^esub> u = afun w \<cdot>\<^sub>o a"
      using qf j by (rule final_functor_obtain)
    have v: "\<langle>a, dg (atgt w) \<cdot>\<^sub>a u\<rangle> \<in> cverts C (asrc w) (dg (atgt w) \<cdot>\<^sub>o j)"
      using X u a Fq[OF a] by (simp add: mem_M)
    show ?thesis
      using v W0_inv_at_cc[OF j a u] M_opair by blast
  qed
  show "\<langle>k, f \<circ>\<^bsub>C\<^esub> dg (atgt w) \<cdot>\<^sub>a u\<rangle> \<in> W0_inv_at C w (src\<^bsub>ix (atgt w)\<^esub> u)"
    if u: "u \<in> Arr (ix (atgt w))" and "M k" and "M f"
      and kf: "\<langle>k, f\<rangle> \<in> W0_inv_at C w (tgt\<^bsub>ix (atgt w)\<^esub> u)" for u k f
  proof -
    let ?X = "atgt w" and ?F = "dg (atgt w)" and ?q = "afun w"
    let ?s = "src\<^bsub>ix ?X\<^esub> u" and ?t = "tgt\<^bsub>ix ?X\<^esub> u"
    let ?Es = "cgraph C ?X (?F \<cdot>\<^sub>o ?s)"
    have st: "?s \<in> Ob (ix ?X)" "?t \<in> Ob (ix ?X)"
      using cJ u by simp_all
    note kfD = mem_W0_inv_at[OF mem_M[OF st(2)] \<open>M k\<close> \<open>M f\<close>, THEN iffD1, OF kf]
    have k: "k \<in> Ob (ix (asrc w))" and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = ?F \<cdot>\<^sub>o ?t"
      "tgt\<^bsub>C\<^esub> f = dg (asrc w) \<cdot>\<^sub>o k"
      and c1: "conn (cgraph C ?X (?F \<cdot>\<^sub>o ?t)) \<langle>?q \<cdot>\<^sub>o k, f\<rangle> \<langle>?t, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?t)\<rangle>"
      using kfD by blast+
    have Fu: "?F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?s" "tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?t"
      using X u by simp_all
    have "conn (cgraph C ?X (src\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u)))
        \<langle>?q \<cdot>\<^sub>o k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<langle>?t, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?t) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle>"
      by (rule comma_conn_precomp[OF M_ix ls cJ C FX Fu(1) Fu(3) M_obj \<open>M f\<close> M_tgt M_idt c1])
    then have c2: "conn ?Es \<langle>?q \<cdot>\<^sub>o k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<langle>?t, ?F \<cdot>\<^sub>a u\<rangle>"
      using C Fu by simp
    have ids: "id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s) \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)) = ?F \<cdot>\<^sub>o ?s"
      "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)) = ?F \<cdot>\<^sub>o ?s"
      using C X st by simp_all
    have "\<langle>\<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>, \<langle>?t, ?F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>\<rangle> \<in> ?Es"
      by (rule comma_edgesI[OF u ids])
    moreover have "?F \<cdot>\<^sub>a u \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s) = ?F \<cdot>\<^sub>a u"
      using C Fu by simp
    ultimately have "\<langle>\<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>, \<langle>?t, ?F \<cdot>\<^sub>a u\<rangle>\<rangle> \<in> ?Es"
      by simp
    then have c3: "conn ?Es \<langle>?t, ?F \<cdot>\<^sub>a u\<rangle> \<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>"
      by (rule conn_edge_rev[OF _ M_opair M_opair])
    have c: "conn ?Es \<langle>?q \<cdot>\<^sub>o k, f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<langle>?s, id\<^bsub>C\<^esub> (?F \<cdot>\<^sub>o ?s)\<rangle>"
      using c2 c3 by (rule conn_trans)
    have fu: "f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u \<in> Arr C" "src\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u) = ?F \<cdot>\<^sub>o ?s"
      "tgt\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u) = dg (asrc w) \<cdot>\<^sub>o k"
      using C f Fu by simp_all
    show ?thesis
      using mem_W0_inv_at[OF mem_M[OF st(1)] \<open>M k\<close> M_ccomp] k fu c by blast
  qed
qed

text \<open>The image of \<open>w\<close> under the colimit functor, read at \<open>j'\<close>.\<close>

lemma colim_W0_PArr: "colim_functor C \<cdot>\<^sub>a w \<in> PArr C"
  using C ls wD by simp

lemma colim_W0_body:
  assumes "j \<in> Ob (ix (asrc w))"
  shows "body (colim_functor C \<cdot>\<^sub>a w) \<cdot> j =
    cc (cgraph C (atgt w) (dg (asrc w) \<cdot>\<^sub>o j)) \<langle>afun w \<cdot>\<^sub>o j, id\<^bsub>C\<^esub> (dg (asrc w) \<cdot>\<^sub>o j)\<rangle>"
  using C ls wD w assms by simp

text \<open>
  \<open>\<psi> \<circ> \<phi> = id\<close>: at \<open>j'\<close>, \<open>\<langle>q j', id\<rangle>\<close> is in \<open>\<phi>\<close> at \<open>j'\<close> and \<open>\<langle>j', id\<rangle>\<close> is in \<open>\<psi>\<close> at \<open>q j'\<close>, so the
  composite at \<open>j'\<close> contains \<open>\<langle>j', id\<rangle>\<close>, as the identity does.
\<close>

lemma W0_inv_left: "Pcomp C (W0_inv C w) (colim_functor C \<cdot>\<^sub>a w) = Pid C (asrc w)"
proof -
  let ?\<phi> = "colim_functor C \<cdot>\<^sub>a w" and ?\<psi> = "W0_inv C w" and ?X' = "asrc w"
  have \<phi>: "?\<phi> \<in> PArr C"
    by (rule colim_W0_PArr)
  have \<psi>: "?\<psi> \<in> PArr C"
    by (rule W0_inv_PArr)
  have \<psi>\<phi>: "asrc ?\<psi> = atgt ?\<phi>"
    using wD by simp
  have comp: "Pcomp C ?\<psi> ?\<phi> \<in> PArr C"
    using cat_comp[OF PSh_category[OF C ls], of ?\<phi> ?\<psi>] \<phi> \<psi> \<psi>\<phi> by simp
  have idP: "Pid C ?X' \<in> PArr C"
    using C ls X' by simp
  have src_eq: "asrc (Pcomp C ?\<psi> ?\<phi>) = asrc (Pid C ?X')"
    using wD X' by (simp add: DOb_M)
  have tgt_eq: "atgt (Pcomp C ?\<psi> ?\<phi>) = atgt (Pid C ?X')"
    using X' by (simp add: DOb_M)
  show ?thesis
  proof (rule PArr_eqI[OF comp idP src_eq tgt_eq])
    fix j
    assume j0: "j \<in> Ob (ix (asrc (Pcomp C ?\<psi> ?\<phi>)))"
    then have j: "j \<in> Ob (ix ?X')"
      using wD by simp
    have j': "j \<in> Ob (ix (asrc ?\<phi>))"
      using wD j by simp
    let ?x = "dg ?X' \<cdot>\<^sub>o j"
    have qj: "afun w \<cdot>\<^sub>o j \<in> Ob (ix (atgt w))"
      using q j by simp
    have Fqj: "dg (atgt w) \<cdot>\<^sub>o (afun w \<cdot>\<^sub>o j) = ?x"
      using Fq[OF j] .
    have x: "?x \<in> Ob C"
      using X' j by simp
    have mem1: "\<langle>afun w \<cdot>\<^sub>o j, id\<^bsub>C\<^esub> ?x\<rangle> \<in> body ?\<phi> \<cdot> j"
      using colim_W0_body[OF j] by simp
    have mem2: "\<langle>j, id\<^bsub>C\<^esub> ?x\<rangle> \<in> body ?\<psi> \<cdot> (afun w \<cdot>\<^sub>o j)"
      using body_W0_inv_app[OF ls wD qj] mem_W0_inv_at[OF mem_M[OF qj] mem_M[OF j] M_idt] j C x Fqj
      by simp
    have M3: "M (afun w \<cdot>\<^sub>o j)" "M (id\<^bsub>C\<^esub> ?x)" "M j"
      using j by (simp_all add: mem_M)
    have "\<langle>j, id\<^bsub>C\<^esub> ?x \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> ?x\<rangle> \<in> body (Pcomp C ?\<psi> ?\<phi>) \<cdot> j"
      unfolding mem_Pcomp_body[OF C ls \<phi> \<psi> \<psi>\<phi> j'] using mem1 mem2 M3 conn_refl M_opair by blast
    then have in_comp: "\<langle>j, id\<^bsub>C\<^esub> ?x\<rangle> \<in> body (Pcomp C ?\<psi> ?\<phi>) \<cdot> j"
      using C x by simp
    have in_id: "\<langle>j, id\<^bsub>C\<^esub> ?x\<rangle> \<in> body (Pid C ?X') \<cdot> j"
      using C ls X' j by simp
    show "body (Pcomp C ?\<psi> ?\<phi>) \<cdot> j = body (Pid C ?X') \<cdot> j"
      by (rule PArr_body_share[OF C ls comp idP src_eq tgt_eq j0 in_comp in_id])
  qed
qed

text \<open>
  \<open>\<phi> \<circ> \<psi> = id\<close>: at \<open>j\<close>, take \<open>u : j \<rightarrow> q a\<close>; \<open>\<langle>a, F u\<rangle>\<close> is in \<open>\<psi>\<close> at \<open>j\<close> and \<open>\<langle>q a, id\<rangle>\<close> in \<open>\<phi>\<close> at \<open>a\<close>,
  so the composite at \<open>j\<close> contains \<open>\<langle>q a, F u\<rangle>\<close>, which the edge \<open>u\<close> joins to \<open>\<langle>j, id\<rangle>\<close>.
\<close>

lemma W0_inv_right: "Pcomp C (colim_functor C \<cdot>\<^sub>a w) (W0_inv C w) = Pid C (atgt w)"
proof -
  let ?\<phi> = "colim_functor C \<cdot>\<^sub>a w" and ?\<psi> = "W0_inv C w" and ?X = "atgt w"
  have \<phi>: "?\<phi> \<in> PArr C"
    by (rule colim_W0_PArr)
  have \<psi>: "?\<psi> \<in> PArr C"
    by (rule W0_inv_PArr)
  have \<phi>\<psi>: "asrc ?\<phi> = atgt ?\<psi>"
    using wD by simp
  have comp: "Pcomp C ?\<phi> ?\<psi> \<in> PArr C"
    using cat_comp[OF PSh_category[OF C ls], of ?\<psi> ?\<phi>] \<phi> \<psi> \<phi>\<psi> by simp
  have idP: "Pid C ?X \<in> PArr C"
    using C ls X by simp
  have src_eq: "asrc (Pcomp C ?\<phi> ?\<psi>) = asrc (Pid C ?X)"
    using X by (simp add: DOb_M)
  have tgt_eq: "atgt (Pcomp C ?\<phi> ?\<psi>) = atgt (Pid C ?X)"
    using wD X by (simp add: DOb_M)
  show ?thesis
  proof (rule PArr_eqI[OF comp idP src_eq tgt_eq])
    fix j
    assume j0: "j \<in> Ob (ix (asrc (Pcomp C ?\<phi> ?\<psi>)))"
    then have j: "j \<in> Ob (ix ?X)"
      by simp
    have j': "j \<in> Ob (ix (asrc ?\<psi>))"
      using j by simp
    let ?F = "dg ?X"
    obtain a u where a: "a \<in> Ob (ix (asrc w))" and u: "u \<in> Arr (ix ?X)"
      "src\<^bsub>ix ?X\<^esub> u = j" "tgt\<^bsub>ix ?X\<^esub> u = afun w \<cdot>\<^sub>o a"
      using qf j by (rule final_functor_obtain)
    have Fu: "?F \<cdot>\<^sub>a u \<in> Arr C" "tgt\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a u) = dg (asrc w) \<cdot>\<^sub>o a"
      using X u Fq[OF a] by simp_all
    have mem1: "\<langle>a, ?F \<cdot>\<^sub>a u\<rangle> \<in> body ?\<psi> \<cdot> j"
      using body_W0_inv_app[OF ls wD j] W0_inv_at_cc[OF j a u] by (simp add: mem_M[OF a])
    have mem2: "\<langle>afun w \<cdot>\<^sub>o a, id\<^bsub>C\<^esub> (dg (asrc w) \<cdot>\<^sub>o a)\<rangle> \<in> body ?\<phi> \<cdot> a"
      using colim_W0_body[OF a] by simp
    have M3: "M a" "M (?F \<cdot>\<^sub>a u)" "M (afun w \<cdot>\<^sub>o a)" "M (id\<^bsub>C\<^esub> (dg (asrc w) \<cdot>\<^sub>o a))"
      using a by (simp_all add: mem_M)
    have "\<langle>afun w \<cdot>\<^sub>o a, id\<^bsub>C\<^esub> (dg (asrc w) \<cdot>\<^sub>o a) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle> \<in> body (Pcomp C ?\<phi> ?\<psi>) \<cdot> j"
      unfolding mem_Pcomp_body[OF C ls \<psi> \<phi> \<phi>\<psi> j'] using mem1 mem2 M3 conn_refl M_opair by blast
    then have in_comp: "\<langle>afun w \<cdot>\<^sub>o a, ?F \<cdot>\<^sub>a u\<rangle> \<in> body (Pcomp C ?\<phi> ?\<psi>) \<cdot> j"
      using C Fu by simp
    have in_id: "\<langle>afun w \<cdot>\<^sub>o a, ?F \<cdot>\<^sub>a u\<rangle> \<in> body (Pid C ?X) \<cdot> j"
      using C ls X j hub(1)[OF j a u] by simp
    show "body (Pcomp C ?\<phi> ?\<psi>) \<cdot> j = body (Pid C ?X) \<cdot> j"
      by (rule PArr_body_share[OF C ls comp idP src_eq tgt_eq j0 in_comp in_id])
  qed
qed

end

subsection \<open>The theorem\<close>

theorem colim_inverts_W0:
  assumes "category C" and "locally_small C"
  shows "inverts (colim_functor C) (W0 C) (PSh C)"
  unfolding inverts_def
proof (intro allI impI)
  fix w
  assume "M w" and w: "w \<in> W0 C"
  have wD: "w \<in> DArr C"
    using w by simp
  note \<phi> = colim_W0_PArr[OF assms w] and \<psi> = W0_inv_PArr[OF assms w]
  show "iso (PSh C) (colim_functor C \<cdot>\<^sub>a w)"
  proof (rule isoI[where g = "W0_inv C w"])
    show "W0_inv C w \<circ>\<^bsub>PSh C\<^esub> colim_functor C \<cdot>\<^sub>a w = id\<^bsub>PSh C\<^esub> (src\<^bsub>PSh C\<^esub> (colim_functor C \<cdot>\<^sub>a w))"
      using \<phi> \<psi> wD W0_inv_left[OF assms w] by simp
    show "colim_functor C \<cdot>\<^sub>a w \<circ>\<^bsub>PSh C\<^esub> W0_inv C w = id\<^bsub>PSh C\<^esub> (tgt\<^bsub>PSh C\<^esub> (colim_functor C \<cdot>\<^sub>a w))"
      using \<phi> \<psi> wD W0_inv_right[OF assms w] by simp
  qed (use \<phi> \<psi> wD in simp_all)
qed

end
