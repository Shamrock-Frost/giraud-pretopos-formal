section \<open>The presheaf model is a category\<close>

theory PSh_Category
  imports PSh_Basics
begin

subsection \<open>Composition does not depend on representatives\<close>

text \<open>
  Let \<open>a : X \<rightarrow> Y\<close> and \<open>b : Y \<rightarrow> Z\<close> be arrows, \<open>j\<close> an object of \<open>ix X\<close>, \<open>\<langle>k, f\<rangle>\<close> an element of
  \<open>body a \<cdot> j\<close> and \<open>\<langle>l, g\<rangle>\<close> an element of \<open>body b \<cdot> k\<close>. Then \<open>body (Pcomp C b a) \<cdot> j\<close> is the
  component of \<open>\<langle>l, g \<circ> f\<rangle>\<close>. Two choices of \<open>\<langle>l, g\<rangle>\<close> for the same \<open>\<langle>k, f\<rangle>\<close> are connected in
  \<open>(dg Y \<cdot>\<^sub>o k \<down> dg Z)\<close>, so precomposing with \<open>f\<close> keeps them connected. Along an edge
  \<open>\<langle>k, f\<rangle> \<rightarrow> \<langle>k', dg Y \<cdot>\<^sub>a c \<circ> f\<rangle>\<close> of \<open>(dg X \<cdot>\<^sub>o j \<down> dg Y)\<close>, an element \<open>\<langle>l', g'\<rangle>\<close> of \<open>body b \<cdot> k'\<close> gives
  the element \<open>\<langle>l', g' \<circ> dg Y \<cdot>\<^sub>a c\<rangle>\<close> of \<open>body b \<cdot> k\<close>, with the same composite. So the component
  of \<open>\<langle>l, g \<circ> f\<rangle>\<close> does not change along \<open>body a \<cdot> j\<close>, by induction along it.
\<close>

lemma PArr_body_conn_precomp:
  assumes C: "category C" and ls: "locally_small C" and b: "b \<in> PArr C"
    and k: "k \<in> Ob (ix (asrc b))"
    and lg: "\<langle>l, g\<rangle> \<in> body b \<cdot> k" and lg': "\<langle>l', g'\<rangle> \<in> body b \<cdot> k"
    and "M l" and "M g" and "M l'" and "M g'"
    and h: "h \<in> Arr C" "tgt\<^bsub>C\<^esub> h = dg (asrc b) \<cdot>\<^sub>o k"
  shows "conn (cgraph C (atgt b) (src\<^bsub>C\<^esub> h)) \<langle>l, g \<circ>\<^bsub>C\<^esub> h\<rangle> \<langle>l', g' \<circ>\<^bsub>C\<^esub> h\<rangle>"
proof -
  have Z: "atgt b \<in> DOb C"
    using b by simp
  have c: "conn (cgraph C (atgt b) (dg (asrc b) \<cdot>\<^sub>o k)) \<langle>l, g\<rangle> \<langle>l', g'\<rangle>"
    by (rule PArr_body_conn[OF C ls b k lg lg'])
  show ?thesis
    by (rule comma_conn_precomp[OF M_ix ls DOb_category[OF Z] C DOb_functor[OF Z] h
          \<open>M l\<close> \<open>M g\<close> \<open>M l'\<close> \<open>M g'\<close> c])
qed

lemma Pcomp_body_eq:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C" and b: "b \<in> PArr C"
    and ab: "asrc b = atgt a" and j: "j \<in> Ob (ix (asrc a))"
    and kf: "\<langle>k, f\<rangle> \<in> body a \<cdot> j" and lg: "\<langle>l, g\<rangle> \<in> body b \<cdot> k"
    and Mk: "M k" and Mf: "M f" and Ml: "M l" and Mg: "M g"
  shows "body (Pcomp C b a) \<cdot> j = cc (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  let ?Y = "asrc b" and ?Z = "atgt b"
  let ?x = "dg (asrc a) \<cdot>\<^sub>o j"
  let ?E = "cgraph C ?Z ?x" and ?Ea = "cgraph C (atgt a) ?x"
  let ?w0 = "\<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
  have MEa: "M ?Ea"
    using C ls a j by simp
  have cY: "category (ix ?Y)"
    using b by simp
  have GY: "is_functor (dg ?Y) (ix ?Y) C"
    using PArr_asrc[OF b] by (rule DOb_functor)
  have a_pair: "k' \<in> Ob (ix ?Y) \<and> f' \<in> Arr C \<and> src\<^bsub>C\<^esub> f' = ?x \<and> tgt\<^bsub>C\<^esub> f' = dg ?Y \<cdot>\<^sub>o k'"
    if "\<langle>k', f'\<rangle> \<in> body a \<cdot> j" and "M k'" and "M f'" for k' f'
    using PArr_body_pair[OF C ls a j that] ab by simp
  have b_pair: "g' \<in> Arr C \<and> src\<^bsub>C\<^esub> g' = dg ?Y \<cdot>\<^sub>o k'"
    if "k' \<in> Ob (ix ?Y)" and "\<langle>l', g'\<rangle> \<in> body b \<cdot> k'" and "M l'" and "M g'" for k' l' g'
    using PArr_body_pair[OF C ls b that] by simp
  have k: "k \<in> Ob (ix ?Y)" and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = ?x" "tgt\<^bsub>C\<^esub> f = dg ?Y \<cdot>\<^sub>o k"
    using a_pair[OF kf Mk Mf] by simp_all
  define P where "P = (\<lambda>v. \<forall>\<^sub>s l' g'. \<langle>l', g'\<rangle> \<in> body b \<cdot> pfst v \<longrightarrow>
    conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> psnd v\<rangle>)"
  have dP: "dfn P"
    unfolding P_def by dfn
  have P0: "P \<langle>k, f\<rangle>"
  proof -
    have "conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> f\<rangle>" if "M l'" and "M g'" and lg': "\<langle>l', g'\<rangle> \<in> body b \<cdot> k"
      for l' g'
      using PArr_body_conn_precomp[OF C ls b k lg lg' Ml Mg that(1,2) f(1) f(3)]
      unfolding f(2) .
    then show ?thesis
      unfolding P_def using Mk Mf by auto
  qed
  have step: "P a' \<longleftrightarrow> P b'"
    if Ma: "M a'" and Mb: "M b'" and e: "\<langle>a', b'\<rangle> \<in> ?Ea" and "conn ?Ea \<langle>k, f\<rangle> a'" for a' b'
  proof -
    obtain f' c where a': "a' = \<langle>src\<^bsub>ix ?Y\<^esub> c, f'\<rangle>"
      and b': "b' = \<langle>tgt\<^bsub>ix ?Y\<^esub> c, dg ?Y \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> f'\<rangle>" and c: "c \<in> Arr (ix ?Y)"
      and f': "f' \<in> Arr C" "src\<^bsub>C\<^esub> f' = ?x" "tgt\<^bsub>C\<^esub> f' = dg ?Y \<cdot>\<^sub>o src\<^bsub>ix ?Y\<^esub> c"
      using e Ma Mb unfolding ab[symmetric] by (rule comma_edge_pairE)
    let ?s = "src\<^bsub>ix ?Y\<^esub> c" and ?t = "tgt\<^bsub>ix ?Y\<^esub> c" and ?Gc = "dg ?Y \<cdot>\<^sub>a c"
    have st: "?s \<in> Ob (ix ?Y)" "?t \<in> Ob (ix ?Y)"
      using cY c by simp_all
    have Gc: "?Gc \<in> Arr C" "src\<^bsub>C\<^esub> ?Gc = dg ?Y \<cdot>\<^sub>o ?s" "tgt\<^bsub>C\<^esub> ?Gc = dg ?Y \<cdot>\<^sub>o ?t"
      using GY c by simp_all
    have Pa: "P a' \<longleftrightarrow> (\<forall>\<^sub>s l' g'. \<langle>l', g'\<rangle> \<in> body b \<cdot> ?s \<longrightarrow> conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>)"
      unfolding P_def a' using f'(1) by (simp add: mem_M)
    have Pb: "P b' \<longleftrightarrow>
        (\<forall>\<^sub>s l' g'. \<langle>l', g'\<rangle> \<in> body b \<cdot> ?t \<longrightarrow> conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> (?Gc \<circ>\<^bsub>C\<^esub> f')\<rangle>)"
      unfolding P_def b' by simp
    have bc: "\<langle>l', g' \<circ>\<^bsub>C\<^esub> ?Gc\<rangle> \<in> body b \<cdot> ?s"
      if "\<langle>l', g'\<rangle> \<in> body b \<cdot> ?t" and "M l'" and "M g'" for l' g'
      by (rule PArr_compat[OF b c that(2,3,1)])
    have assoc: "g' \<circ>\<^bsub>C\<^esub> (?Gc \<circ>\<^bsub>C\<^esub> f') = (g' \<circ>\<^bsub>C\<^esub> ?Gc) \<circ>\<^bsub>C\<^esub> f'"
      if "\<langle>l', g'\<rangle> \<in> body b \<cdot> ?t" and "M l'" and "M g'" for l' g'
    proof -
      have g': "g' \<in> Arr C" "src\<^bsub>C\<^esub> g' = dg ?Y \<cdot>\<^sub>o ?t"
        using b_pair[OF st(2) that] by simp_all
      show ?thesis
        using cat_assoc[OF C f'(1) Gc(1) g'(1)] f'(3) Gc(2,3) g'(2) by simp
    qed
    show ?thesis
      unfolding Pa Pb
    proof
      assume A: "\<forall>\<^sub>s l' g'. \<langle>l', g'\<rangle> \<in> body b \<cdot> ?s \<longrightarrow> conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
      show "\<forall>\<^sub>s l' g'. \<langle>l', g'\<rangle> \<in> body b \<cdot> ?t \<longrightarrow> conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> (?Gc \<circ>\<^bsub>C\<^esub> f')\<rangle>"
      proof (intro allI impI)
        fix l' g'
        assume "M l'" and "M g'" and lg': "\<langle>l', g'\<rangle> \<in> body b \<cdot> ?t"
        have "conn ?E ?w0 \<langle>l', (g' \<circ>\<^bsub>C\<^esub> ?Gc) \<circ>\<^bsub>C\<^esub> f'\<rangle>"
          using A bc[OF lg' \<open>M l'\<close> \<open>M g'\<close>] \<open>M l'\<close> M_ccomp by blast
        then show "conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> (?Gc \<circ>\<^bsub>C\<^esub> f')\<rangle>"
          unfolding assoc[OF lg' \<open>M l'\<close> \<open>M g'\<close>] .
      qed
    next
      assume B: "\<forall>\<^sub>s l' g'. \<langle>l', g'\<rangle> \<in> body b \<cdot> ?t \<longrightarrow> conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> (?Gc \<circ>\<^bsub>C\<^esub> f')\<rangle>"
      show "\<forall>\<^sub>s l' g'. \<langle>l', g'\<rangle> \<in> body b \<cdot> ?s \<longrightarrow> conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
      proof (intro allI impI)
        fix l' g'
        assume "M l'" and "M g'" and lg': "\<langle>l', g'\<rangle> \<in> body b \<cdot> ?s"
        obtain l'' g'' where lg'': "\<langle>l'', g''\<rangle> \<in> body b \<cdot> ?t" and "M l''" and "M g''"
          by (rule PArr_body_ex[OF b st(2)]) blast
        have "conn ?E ?w0 \<langle>l'', g'' \<circ>\<^bsub>C\<^esub> (?Gc \<circ>\<^bsub>C\<^esub> f')\<rangle>"
          using B lg'' \<open>M l''\<close> \<open>M g''\<close> by blast
        then have c1: "conn ?E ?w0 \<langle>l'', (g'' \<circ>\<^bsub>C\<^esub> ?Gc) \<circ>\<^bsub>C\<^esub> f'\<rangle>"
          unfolding assoc[OF lg'' \<open>M l''\<close> \<open>M g''\<close>] .
        have c2: "conn ?E \<langle>l'', (g'' \<circ>\<^bsub>C\<^esub> ?Gc) \<circ>\<^bsub>C\<^esub> f'\<rangle> \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
          using PArr_body_conn_precomp[OF C ls b st(1) bc[OF lg'' \<open>M l''\<close> \<open>M g''\<close>] lg'
              \<open>M l''\<close> M_ccomp \<open>M l'\<close> \<open>M g'\<close> f'(1) f'(3)]
          unfolding f'(2) .
        show "conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
          by (rule conn_trans[OF c1 c2])
      qed
    qed
  qed
  have inv: "conn ?E ?w0 \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle>"
    if kf': "\<langle>k', f'\<rangle> \<in> body a \<cdot> j" and lg': "\<langle>l', g'\<rangle> \<in> body b \<cdot> k'"
      and "M k'" and "M f'" and "M l'" and "M g'" for k' f' l' g'
  proof -
    have "conn ?Ea \<langle>k, f\<rangle> \<langle>k', f'\<rangle>"
      by (rule PArr_body_conn[OF C ls a j kf kf'])
    then have "P \<langle>k', f'\<rangle>"
      by (rule conn_induct[OF MEa M_opair _ dP P0 step])
    then show ?thesis
      unfolding P_def using \<open>M k'\<close> \<open>M f'\<close> \<open>M l'\<close> \<open>M g'\<close> lg' by simp
  qed
  show ?thesis
  proof (rule cls_eqI)
    fix w
    assume "w \<in> body (Pcomp C b a) \<cdot> j"
    then obtain k' f' l' g' where "M w" and "M k'" and "M f'" and "M l'" and "M g'"
      and kf': "\<langle>k', f'\<rangle> \<in> body a \<cdot> j" and lg': "\<langle>l', g'\<rangle> \<in> body b \<cdot> k'"
      and c: "conn ?E \<langle>l', g' \<circ>\<^bsub>C\<^esub> f'\<rangle> w"
      unfolding mem_Pcomp_body[OF C ls a b ab j] by blast
    have "conn ?E ?w0 w"
      using conn_trans[OF inv[OF kf' lg' \<open>M k'\<close> \<open>M f'\<close> \<open>M l'\<close> \<open>M g'\<close>] c] .
    then show "w \<in> cc ?E ?w0"
      using \<open>M w\<close> by simp
  next
    fix w
    assume "w \<in> cc ?E ?w0"
    then have "M w" and "conn ?E ?w0 w"
      by simp_all
    then show "w \<in> body (Pcomp C b a) \<cdot> j"
      unfolding mem_Pcomp_body[OF C ls a b ab j] using kf lg Mk Mf Ml Mg by blast
  qed
qed

subsection \<open>Composites are arrows\<close>

text \<open>
  The value of a composite at \<open>j\<close> is a component by the key lemma. It is compatible with an
  arrow \<open>u\<close> of the index category because \<open>a\<close> is: a representative \<open>\<langle>l, g \<circ> f\<rangle>\<close> at the target of
  \<open>u\<close>, with \<open>\<langle>k, f\<rangle>\<close> in \<open>body a\<close>, gives the representative \<open>\<langle>l, g \<circ> (f \<circ> dg X \<cdot>\<^sub>a u)\<rangle>\<close> at its source.
\<close>

lemma Pcomp_eta: "Pcomp C b a = \<langle>\<langle>asrc a, atgt b\<rangle>, body (Pcomp C b a)\<rangle>"
  by (simp add: Pcomp_def)

lemma Pcomp_PArr [simp]:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C" and b: "b \<in> PArr C"
    and ab: "asrc b = atgt a"
  shows "Pcomp C b a \<in> PArr C"
proof -
  let ?X = "asrc a" and ?Z = "atgt b"
  have X: "?X \<in> DOb C" and Z: "?Z \<in> DOb C"
    using a b by simp_all
  have cX: "category (ix ?X)"
    using a by simp
  have "\<langle>\<langle>?X, ?Z\<rangle>, body (Pcomp C b a)\<rangle> \<in> PArr C"
  proof (rule PArrI[OF X Z])
    show "body (Pcomp C b a) = (\<lambda>j\<in>Ob (ix ?X). body (Pcomp C b a) \<cdot> j)"
      by (rule trans[OF body_Pcomp Lam_eqI]) (rule Pcomp_body_app[OF C ls a b ab, symmetric])
    show "\<exists>\<^sub>s v. v \<in> cverts C ?Z (dg ?X \<cdot>\<^sub>o j) \<and>
        body (Pcomp C b a) \<cdot> j = cc (cgraph C ?Z (dg ?X \<cdot>\<^sub>o j)) v"
      if j: "j \<in> Ob (ix ?X)" for j
    proof -
      obtain k f where kf: "\<langle>k, f\<rangle> \<in> body a \<cdot> j" and "M k" and "M f"
        and k: "k \<in> Ob (ix (atgt a))" and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = dg ?X \<cdot>\<^sub>o j"
        and "tgt\<^bsub>C\<^esub> f = dg (atgt a) \<cdot>\<^sub>o k"
        using a j by (rule PArr_body_ex)
      have k': "k \<in> Ob (ix (asrc b))"
        using k ab by simp
      obtain l g where lg: "\<langle>l, g\<rangle> \<in> body b \<cdot> k" and "M l" and "M g"
        and "l \<in> Ob (ix ?Z)" and "g \<in> Arr C" and "src\<^bsub>C\<^esub> g = dg (asrc b) \<cdot>\<^sub>o k"
        and "tgt\<^bsub>C\<^esub> g = dg ?Z \<cdot>\<^sub>o l"
        using b k' by (rule PArr_body_ex)
      have "\<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> \<in> cverts C ?Z (dg ?X \<cdot>\<^sub>o j)"
        by (rule Pcomp_vert[OF C ls a b ab j kf lg \<open>M k\<close> \<open>M f\<close> \<open>M l\<close> \<open>M g\<close>])
      moreover have "body (Pcomp C b a) \<cdot> j = cc (cgraph C ?Z (dg ?X \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle>"
        by (rule Pcomp_body_eq[OF C ls a b ab j kf lg \<open>M k\<close> \<open>M f\<close> \<open>M l\<close> \<open>M g\<close>])
      ultimately show ?thesis
        using M_opair by blast
    qed
    show "\<langle>k, f \<circ>\<^bsub>C\<^esub> dg ?X \<cdot>\<^sub>a u\<rangle> \<in> body (Pcomp C b a) \<cdot> src\<^bsub>ix ?X\<^esub> u"
      if u: "u \<in> Arr (ix ?X)" and "M k" and "M f"
        and kf: "\<langle>k, f\<rangle> \<in> body (Pcomp C b a) \<cdot> tgt\<^bsub>ix ?X\<^esub> u" for u k f
    proof -
      let ?s = "src\<^bsub>ix ?X\<^esub> u" and ?t = "tgt\<^bsub>ix ?X\<^esub> u" and ?Fu = "dg ?X \<cdot>\<^sub>a u"
      have st: "?s \<in> Ob (ix ?X)" "?t \<in> Ob (ix ?X)"
        using cX u by simp_all
      have Fu: "?Fu \<in> Arr C" "src\<^bsub>C\<^esub> ?Fu = dg ?X \<cdot>\<^sub>o ?s" "tgt\<^bsub>C\<^esub> ?Fu = dg ?X \<cdot>\<^sub>o ?t"
        using X u by simp_all
      obtain k1 f1 l1 g1 where "M k1" and "M f1" and "M l1" and "M g1"
        and kf1: "\<langle>k1, f1\<rangle> \<in> body a \<cdot> ?t" and lg1: "\<langle>l1, g1\<rangle> \<in> body b \<cdot> k1"
        and c: "conn (cgraph C ?Z (dg ?X \<cdot>\<^sub>o ?t)) \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> f1\<rangle> \<langle>k, f\<rangle>"
        using kf unfolding mem_Pcomp_body[OF C ls a b ab st(2)] by blast
      have f1: "f1 \<in> Arr C" "src\<^bsub>C\<^esub> f1 = dg ?X \<cdot>\<^sub>o ?t" "tgt\<^bsub>C\<^esub> f1 = dg (asrc b) \<cdot>\<^sub>o k1"
        and k1: "k1 \<in> Ob (ix (asrc b))"
        using PArr_body_pair[OF C ls a st(2) kf1 \<open>M k1\<close> \<open>M f1\<close>] ab by simp_all
      have g1: "g1 \<in> Arr C" "src\<^bsub>C\<^esub> g1 = dg (asrc b) \<cdot>\<^sub>o k1"
        using PArr_body_pair[OF C ls b k1 lg1 \<open>M l1\<close> \<open>M g1\<close>] by simp_all
      have kf1': "\<langle>k1, f1 \<circ>\<^bsub>C\<^esub> ?Fu\<rangle> \<in> body a \<cdot> ?s"
        by (rule PArr_compat[OF a u \<open>M k1\<close> \<open>M f1\<close> kf1])
      have "conn (cgraph C ?Z (dg ?X \<cdot>\<^sub>o ?s)) \<langle>l1, (g1 \<circ>\<^bsub>C\<^esub> f1) \<circ>\<^bsub>C\<^esub> ?Fu\<rangle> \<langle>k, f \<circ>\<^bsub>C\<^esub> ?Fu\<rangle>"
        using comma_conn_precomp[OF M_ix ls DOb_category[OF Z] C DOb_functor[OF Z] Fu(1) Fu(3)
            \<open>M l1\<close> M_ccomp \<open>M k\<close> \<open>M f\<close> c]
        unfolding Fu(2) .
      moreover have "(g1 \<circ>\<^bsub>C\<^esub> f1) \<circ>\<^bsub>C\<^esub> ?Fu = g1 \<circ>\<^bsub>C\<^esub> (f1 \<circ>\<^bsub>C\<^esub> ?Fu)"
        using cat_assoc[OF C Fu(1) f1(1) g1(1)] Fu(3) f1(2,3) g1(2) by simp
      ultimately have "conn (cgraph C ?Z (dg ?X \<cdot>\<^sub>o ?s)) \<langle>l1, g1 \<circ>\<^bsub>C\<^esub> (f1 \<circ>\<^bsub>C\<^esub> ?Fu)\<rangle> \<langle>k, f \<circ>\<^bsub>C\<^esub> ?Fu\<rangle>"
        by simp
      then show ?thesis
        unfolding mem_Pcomp_body[OF C ls a b ab st(1)]
        using kf1' lg1 \<open>M k1\<close> \<open>M l1\<close> \<open>M g1\<close> M_ccomp M_opair by blast
    qed
  qed
  then show ?thesis
    by (simp only: Pcomp_eta[symmetric])
qed

subsection \<open>Unit and associativity laws\<close>

text \<open>
  Each law is an equality of arrows by \<open>PArr_eqI\<close>; at an object \<open>j\<close> both sides are the component
  of one vertex, computed by the key lemma from representatives, and the vertices agree by the
  unit and associativity laws of \<open>C\<close>.
\<close>

lemma Pcomp_Pid_right:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C"
  shows "Pcomp C a (Pid C (asrc a)) = a"
proof -
  let ?X = "asrc a"
  have X: "?X \<in> DOb C"
    using a by simp
  have i: "Pid C ?X \<in> PArr C"
    using C ls X by simp
  have ia: "asrc a = atgt (Pid C ?X)"
    by simp
  show ?thesis
  proof (rule PArr_eqI[OF Pcomp_PArr[OF C ls i a ia] a])
    show "asrc (Pcomp C a (Pid C ?X)) = asrc a"
      by simp
    show "atgt (Pcomp C a (Pid C ?X)) = atgt a"
      by simp
    fix j
    assume "j \<in> Ob (ix (asrc (Pcomp C a (Pid C ?X))))"
    then have j: "j \<in> Ob (ix ?X)"
      by simp
    have j': "j \<in> Ob (ix (asrc (Pid C ?X)))"
      using j by simp
    have idj: "\<langle>j, id\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>o j)\<rangle> \<in> body (Pid C ?X) \<cdot> j"
      using C ls X j by simp
    obtain l g where lg: "\<langle>l, g\<rangle> \<in> body a \<cdot> j" and "M l" and "M g"
      and "l \<in> Ob (ix (atgt a))" and "g \<in> Arr C" and g: "src\<^bsub>C\<^esub> g = dg ?X \<cdot>\<^sub>o j"
      and "tgt\<^bsub>C\<^esub> g = dg (atgt a) \<cdot>\<^sub>o l"
      using a j by (rule PArr_body_ex)
    have "body (Pcomp C a (Pid C ?X)) \<cdot> j =
        cc (cgraph C (atgt a) (dg (asrc (Pid C ?X)) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>o j)\<rangle>"
      by (rule Pcomp_body_eq[OF C ls i a ia j' idj lg mem_M[OF j] M_idt \<open>M l\<close> \<open>M g\<close>])
    also have "\<dots> = body a \<cdot> j"
      using PArr_body_eq_cc[OF C ls a j lg] C \<open>g \<in> Arr C\<close> g by simp
    finally show "body (Pcomp C a (Pid C ?X)) \<cdot> j = body a \<cdot> j" .
  qed
qed

lemma Pcomp_Pid_left:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> PArr C"
  shows "Pcomp C (Pid C (atgt a)) a = a"
proof -
  let ?Y = "atgt a"
  have Y: "?Y \<in> DOb C"
    using a by simp
  have i: "Pid C ?Y \<in> PArr C"
    using C ls Y by simp
  have ia: "asrc (Pid C ?Y) = atgt a"
    by simp
  show ?thesis
  proof (rule PArr_eqI[OF Pcomp_PArr[OF C ls a i ia] a])
    show "asrc (Pcomp C (Pid C ?Y) a) = asrc a"
      by simp
    show "atgt (Pcomp C (Pid C ?Y) a) = atgt a"
      by simp
    fix j
    assume "j \<in> Ob (ix (asrc (Pcomp C (Pid C ?Y) a)))"
    then have j: "j \<in> Ob (ix (asrc a))"
      by simp
    obtain k f where kf: "\<langle>k, f\<rangle> \<in> body a \<cdot> j" and "M k" and "M f"
      and k: "k \<in> Ob (ix ?Y)" and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j"
      and f: "tgt\<^bsub>C\<^esub> f = dg ?Y \<cdot>\<^sub>o k"
      using a j by (rule PArr_body_ex)
    have idk: "\<langle>k, id\<^bsub>C\<^esub> (dg ?Y \<cdot>\<^sub>o k)\<rangle> \<in> body (Pid C ?Y) \<cdot> k"
      using C ls Y k by simp
    have "body (Pcomp C (Pid C ?Y) a) \<cdot> j =
        cc (cgraph C (atgt (Pid C ?Y)) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>k, id\<^bsub>C\<^esub> (dg ?Y \<cdot>\<^sub>o k) \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule Pcomp_body_eq[OF C ls a i ia j kf idk \<open>M k\<close> \<open>M f\<close> \<open>M k\<close> M_idt])
    also have "\<dots> = body a \<cdot> j"
      using PArr_body_eq_cc[OF C ls a j kf] C \<open>f \<in> Arr C\<close> f by simp
    finally show "body (Pcomp C (Pid C ?Y) a) \<cdot> j = body a \<cdot> j" .
  qed
qed

lemma Pcomp_assoc:
  assumes C: "category C" and ls: "locally_small C"
    and f: "f \<in> PArr C" and g: "g \<in> PArr C" and h: "h \<in> PArr C"
    and fg: "asrc g = atgt f" and gh: "asrc h = atgt g"
  shows "Pcomp C h (Pcomp C g f) = Pcomp C (Pcomp C h g) f"
proof -
  have gf: "Pcomp C g f \<in> PArr C"
    by (rule Pcomp_PArr[OF C ls f g fg])
  have hg: "Pcomp C h g \<in> PArr C"
    by (rule Pcomp_PArr[OF C ls g h gh])
  have gf_h: "asrc h = atgt (Pcomp C g f)"
    using gh by simp
  have f_hg: "asrc (Pcomp C h g) = atgt f"
    using fg by simp
  show ?thesis
  proof (rule PArr_eqI[OF Pcomp_PArr[OF C ls gf h gf_h] Pcomp_PArr[OF C ls f hg f_hg]])
    show "asrc (Pcomp C h (Pcomp C g f)) = asrc (Pcomp C (Pcomp C h g) f)"
      by simp
    show "atgt (Pcomp C h (Pcomp C g f)) = atgt (Pcomp C (Pcomp C h g) f)"
      by simp
    fix j
    assume "j \<in> Ob (ix (asrc (Pcomp C h (Pcomp C g f))))"
    then have j: "j \<in> Ob (ix (asrc f))"
      by simp
    obtain k \<phi> where k\<phi>: "\<langle>k, \<phi>\<rangle> \<in> body f \<cdot> j" and "M k" and "M \<phi>"
      and k0: "k \<in> Ob (ix (atgt f))" and \<phi>: "\<phi> \<in> Arr C" "src\<^bsub>C\<^esub> \<phi> = dg (asrc f) \<cdot>\<^sub>o j"
      "tgt\<^bsub>C\<^esub> \<phi> = dg (atgt f) \<cdot>\<^sub>o k"
      using f j by (rule PArr_body_ex)
    have k: "k \<in> Ob (ix (asrc g))"
      using k0 fg by simp
    obtain l \<gamma> where l\<gamma>: "\<langle>l, \<gamma>\<rangle> \<in> body g \<cdot> k" and "M l" and "M \<gamma>"
      and l0: "l \<in> Ob (ix (atgt g))" and \<gamma>: "\<gamma> \<in> Arr C" "src\<^bsub>C\<^esub> \<gamma> = dg (asrc g) \<cdot>\<^sub>o k"
      "tgt\<^bsub>C\<^esub> \<gamma> = dg (atgt g) \<cdot>\<^sub>o l"
      using g k by (rule PArr_body_ex)
    have l: "l \<in> Ob (ix (asrc h))"
      using l0 gh by simp
    obtain m \<eta> where m\<eta>: "\<langle>m, \<eta>\<rangle> \<in> body h \<cdot> l" and "M m" and "M \<eta>"
      and "m \<in> Ob (ix (atgt h))" and \<eta>: "\<eta> \<in> Arr C" "src\<^bsub>C\<^esub> \<eta> = dg (asrc h) \<cdot>\<^sub>o l"
      "tgt\<^bsub>C\<^esub> \<eta> = dg (atgt h) \<cdot>\<^sub>o m"
      using h l by (rule PArr_body_ex)
    have "body (Pcomp C g f) \<cdot> j = cc (cgraph C (atgt g) (dg (asrc f) \<cdot>\<^sub>o j)) \<langle>l, \<gamma> \<circ>\<^bsub>C\<^esub> \<phi>\<rangle>"
      by (rule Pcomp_body_eq[OF C ls f g fg j k\<phi> l\<gamma> \<open>M k\<close> \<open>M \<phi>\<close> \<open>M l\<close> \<open>M \<gamma>\<close>])
    then have l\<gamma>\<phi>: "\<langle>l, \<gamma> \<circ>\<^bsub>C\<^esub> \<phi>\<rangle> \<in> body (Pcomp C g f) \<cdot> j"
      by simp
    have "body (Pcomp C h g) \<cdot> k = cc (cgraph C (atgt h) (dg (asrc g) \<cdot>\<^sub>o k)) \<langle>m, \<eta> \<circ>\<^bsub>C\<^esub> \<gamma>\<rangle>"
      by (rule Pcomp_body_eq[OF C ls g h gh k l\<gamma> m\<eta> \<open>M l\<close> \<open>M \<gamma>\<close> \<open>M m\<close> \<open>M \<eta>\<close>])
    then have m\<eta>\<gamma>: "\<langle>m, \<eta> \<circ>\<^bsub>C\<^esub> \<gamma>\<rangle> \<in> body (Pcomp C h g) \<cdot> k"
      by simp
    have j1: "j \<in> Ob (ix (asrc (Pcomp C g f)))"
      using j by simp
    have L: "body (Pcomp C h (Pcomp C g f)) \<cdot> j =
        cc (cgraph C (atgt h) (dg (asrc (Pcomp C g f)) \<cdot>\<^sub>o j)) \<langle>m, \<eta> \<circ>\<^bsub>C\<^esub> (\<gamma> \<circ>\<^bsub>C\<^esub> \<phi>)\<rangle>"
      by (rule Pcomp_body_eq[OF C ls gf h gf_h j1 l\<gamma>\<phi> m\<eta> \<open>M l\<close> M_ccomp \<open>M m\<close> \<open>M \<eta>\<close>])
    have R: "body (Pcomp C (Pcomp C h g) f) \<cdot> j =
        cc (cgraph C (atgt (Pcomp C h g)) (dg (asrc f) \<cdot>\<^sub>o j)) \<langle>m, (\<eta> \<circ>\<^bsub>C\<^esub> \<gamma>) \<circ>\<^bsub>C\<^esub> \<phi>\<rangle>"
      by (rule Pcomp_body_eq[OF C ls f hg f_hg j k\<phi> m\<eta>\<gamma> \<open>M k\<close> \<open>M \<phi>\<close> \<open>M m\<close> M_ccomp])
    have assoc: "\<eta> \<circ>\<^bsub>C\<^esub> (\<gamma> \<circ>\<^bsub>C\<^esub> \<phi>) = (\<eta> \<circ>\<^bsub>C\<^esub> \<gamma>) \<circ>\<^bsub>C\<^esub> \<phi>"
      using cat_assoc[OF C \<phi>(1) \<gamma>(1) \<eta>(1)] \<phi>(3) \<gamma>(2,3) \<eta>(2) fg gh by simp
    show "body (Pcomp C h (Pcomp C g f)) \<cdot> j = body (Pcomp C (Pcomp C h g) f) \<cdot> j"
      unfolding L R assoc by simp
  qed
qed

subsection \<open>The theorem\<close>

theorem PSh_category:
  assumes "category C" and "locally_small C"
  shows "category (PSh C)"
  by (rule categoryI)
    (use assms in \<open>simp_all add: mem_M Pcomp_Pid_left Pcomp_Pid_right Pcomp_assoc\<close>)

end
