section \<open>The category of representatives of a morphism of presheaves\<close>

theory Elements
  imports Final_Reindexing PSh_Category
begin

text \<open>
  Construction 3.4 of the note. For a morphism \<open>\<phi> : \<langle>J, F\<rangle> \<rightarrow> \<langle>K, G\<rangle>\<close> of \<open>PSh C\<close>, the category
  \<open>J\<^sub>\<phi>\<close> of all representatives of \<open>\<phi>\<close>: an object is \<open>\<langle>j, \<langle>k, f\<rangle>\<rangle>\<close> with \<open>\<langle>k, f\<rangle>\<close> in the component
  \<open>\<phi> \<cdot> j\<close>, and an arrow \<open>\<langle>j, \<langle>k, f\<rangle>\<rangle> \<rightarrow> \<langle>j', \<langle>k', f'\<rangle>\<rangle>\<close> is a pair of arrows \<open>a : j \<rightarrow> j'\<close>,
  \<open>b : k \<rightarrow> k'\<close> with \<open>G b \<circ> f = f' \<circ> F a\<close>. The projection \<open>q : J\<^sub>\<phi> \<rightarrow> J\<close> is final (Lemma 3.5), so
  \<open>(q, id) : \<langle>J\<^sub>\<phi>, F \<circ> q\<rangle> \<rightarrow> \<langle>J, F\<rangle>\<close> is a final reindexing, and the other projection with the
  family of the \<open>f\<close> is a morphism of diagrams \<open>\<langle>J\<^sub>\<phi>, F \<circ> q\<rangle> \<rightarrow> \<langle>K, G\<rangle>\<close>.

  In the names below, \<open>J\<close> is \<open>ix (asrc \<phi>)\<close>, \<open>F\<close> is \<open>dg (asrc \<phi>)\<close>, \<open>K\<close> is \<open>ix (atgt \<phi>)\<close>, \<open>G\<close> is
  \<open>dg (atgt \<phi>)\<close>. An object \<open>x\<close> has parts \<open>pfst x\<close> (the \<open>j\<close>), \<open>pfst (psnd x)\<close> (the \<open>k\<close>) and
  \<open>psnd (psnd x)\<close> (the \<open>f\<close>); an arrow \<open>e\<close> is \<open>\<langle>\<langle>x, y\<rangle>, \<langle>a, b\<rangle>\<rangle>\<close>.
\<close>

subsection \<open>Definitions\<close>

definition JOb :: "cls \<Rightarrow> cls"
  where "JOb \<phi> = \<lbrace>x. \<exists>\<^sub>s j v. x = \<langle>j, v\<rangle> \<and> j \<in> Ob (ix (asrc \<phi>)) \<and> v \<in> body \<phi> \<cdot> j\<rbrace>"

definition JArr :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "JArr C \<phi> = \<lbrace>e. \<exists>\<^sub>s x y a b. e = \<langle>\<langle>x, y\<rangle>, \<langle>a, b\<rangle>\<rangle> \<and> x \<in> JOb \<phi> \<and> y \<in> JOb \<phi> \<and>
    a \<in> Arr (ix (asrc \<phi>)) \<and> src\<^bsub>ix (asrc \<phi>)\<^esub> a = pfst x \<and> tgt\<^bsub>ix (asrc \<phi>)\<^esub> a = pfst y \<and>
    b \<in> Arr (ix (atgt \<phi>)) \<and> src\<^bsub>ix (atgt \<phi>)\<^esub> b = pfst (psnd x) \<and>
    tgt\<^bsub>ix (atgt \<phi>)\<^esub> b = pfst (psnd y) \<and>
    dg (atgt \<phi>) \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> psnd (psnd x) = psnd (psnd y) \<circ>\<^bsub>C\<^esub> dg (asrc \<phi>) \<cdot>\<^sub>a a\<rbrace>"

definition Jid :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Jid \<phi> x = \<langle>\<langle>x, x\<rangle>, \<langle>id\<^bsub>ix (asrc \<phi>)\<^esub> (pfst x), id\<^bsub>ix (atgt \<phi>)\<^esub> (pfst (psnd x))\<rangle>\<rangle>"

definition Jcomp :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Jcomp \<phi> g h = \<langle>\<langle>pfst (pfst h), psnd (pfst g)\<rangle>,
    \<langle>pfst (psnd g) \<circ>\<^bsub>ix (asrc \<phi>)\<^esub> pfst (psnd h), psnd (psnd g) \<circ>\<^bsub>ix (atgt \<phi>)\<^esub> psnd (psnd h)\<rangle>\<rangle>"

text \<open>The category \<open>J\<^sub>\<phi>\<close>.\<close>

definition Jphi :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Jphi C \<phi> = mkcat (JOb \<phi>) (JArr C \<phi>)
    (\<lambda>e\<in>JArr C \<phi>. pfst (pfst e)) (\<lambda>e\<in>JArr C \<phi>. psnd (pfst e))
    (\<lambda>x\<in>JOb \<phi>. Jid \<phi> x) (\<lambda>p\<in>JArr C \<phi> \<times> JArr C \<phi>. Jcomp \<phi> (pfst p) (psnd p))"

text \<open>The projections \<open>q : J\<^sub>\<phi> \<rightarrow> J\<close> and \<open>\<pi> : J\<^sub>\<phi> \<rightarrow> K\<close>.\<close>

definition qphi :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "qphi C \<phi> = mkfun (\<lambda>x\<in>JOb \<phi>. pfst x) (\<lambda>e\<in>JArr C \<phi>. pfst (psnd e))"

definition piphi :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "piphi C \<phi> = mkfun (\<lambda>x\<in>JOb \<phi>. pfst (psnd x)) (\<lambda>e\<in>JArr C \<phi>. psnd (psnd e))"

text \<open>
  The diagram \<open>X\<^sub>\<phi> = \<langle>J\<^sub>\<phi>, F \<circ> q\<rangle>\<close>, the final reindexing \<open>w\<^sub>\<phi> = (q, id) : X\<^sub>\<phi> \<rightarrow> X\<close>, and
  \<open>t\<^sub>\<phi> = (\<pi>, \<tau>) : X\<^sub>\<phi> \<rightarrow> Y\<close> with \<open>\<tau> \<cdot> \<langle>j, \<langle>k, f\<rangle>\<rangle> = f\<close>.
\<close>

definition Xphi :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Xphi C \<phi> = \<langle>Jphi C \<phi>, fcomp (Jphi C \<phi>) (dg (asrc \<phi>)) (qphi C \<phi>)\<rangle>"

definition wphi :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "wphi C \<phi> = \<langle>\<langle>Xphi C \<phi>, asrc \<phi>\<rangle>,
    \<langle>qphi C \<phi>, \<lambda>x\<in>Ob (Jphi C \<phi>). id\<^bsub>C\<^esub> (dg (asrc \<phi>) \<cdot>\<^sub>o (qphi C \<phi> \<cdot>\<^sub>o x))\<rangle>\<rangle>"

definition tphi :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "tphi C \<phi> = \<langle>\<langle>Xphi C \<phi>, atgt \<phi>\<rangle>, \<langle>piphi C \<phi>, \<lambda>x\<in>Ob (Jphi C \<phi>). psnd (psnd x)\<rangle>\<rangle>"

subsection \<open>Objects and arrows of \<open>J\<^sub>\<phi>\<close> read off\<close>

lemma mem_JOb: "x \<in> JOb \<phi> \<longleftrightarrow> (\<exists>\<^sub>s j v. x = \<langle>j, v\<rangle> \<and> j \<in> Ob (ix (asrc \<phi>)) \<and> v \<in> body \<phi> \<cdot> j)"
  unfolding JOb_def by auto

lemma opair_mem_JOb [simp]:
  "M j \<Longrightarrow> M v \<Longrightarrow> \<langle>j, v\<rangle> \<in> JOb \<phi> \<longleftrightarrow> j \<in> Ob (ix (asrc \<phi>)) \<and> v \<in> body \<phi> \<cdot> j"
  by (auto simp: mem_JOb)

lemma JOb_fst [simp]: "x \<in> JOb \<phi> \<Longrightarrow> pfst x \<in> Ob (ix (asrc \<phi>))"
  by (auto simp: mem_JOb)

lemma JOb_snd [simp]: "x \<in> JOb \<phi> \<Longrightarrow> psnd x \<in> body \<phi> \<cdot> pfst x"
  by (auto simp: mem_JOb)

lemma mem_JArr:
  "e \<in> JArr C \<phi> \<longleftrightarrow> (\<exists>\<^sub>s x y a b. e = \<langle>\<langle>x, y\<rangle>, \<langle>a, b\<rangle>\<rangle> \<and> x \<in> JOb \<phi> \<and> y \<in> JOb \<phi> \<and>
    a \<in> Arr (ix (asrc \<phi>)) \<and> src\<^bsub>ix (asrc \<phi>)\<^esub> a = pfst x \<and> tgt\<^bsub>ix (asrc \<phi>)\<^esub> a = pfst y \<and>
    b \<in> Arr (ix (atgt \<phi>)) \<and> src\<^bsub>ix (atgt \<phi>)\<^esub> b = pfst (psnd x) \<and>
    tgt\<^bsub>ix (atgt \<phi>)\<^esub> b = pfst (psnd y) \<and>
    dg (atgt \<phi>) \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> psnd (psnd x) = psnd (psnd y) \<circ>\<^bsub>C\<^esub> dg (asrc \<phi>) \<cdot>\<^sub>a a)"
  unfolding JArr_def by auto

lemma opair_mem_JArr [simp]:
  "M x \<Longrightarrow> M y \<Longrightarrow> M a \<Longrightarrow> M b \<Longrightarrow> \<langle>\<langle>x, y\<rangle>, \<langle>a, b\<rangle>\<rangle> \<in> JArr C \<phi> \<longleftrightarrow>
    x \<in> JOb \<phi> \<and> y \<in> JOb \<phi> \<and>
    a \<in> Arr (ix (asrc \<phi>)) \<and> src\<^bsub>ix (asrc \<phi>)\<^esub> a = pfst x \<and> tgt\<^bsub>ix (asrc \<phi>)\<^esub> a = pfst y \<and>
    b \<in> Arr (ix (atgt \<phi>)) \<and> src\<^bsub>ix (atgt \<phi>)\<^esub> b = pfst (psnd x) \<and>
    tgt\<^bsub>ix (atgt \<phi>)\<^esub> b = pfst (psnd y) \<and>
    dg (atgt \<phi>) \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> psnd (psnd x) = psnd (psnd y) \<circ>\<^bsub>C\<^esub> dg (asrc \<phi>) \<cdot>\<^sub>a a"
  unfolding mem_JArr by auto

text \<open>The parts of an arrow \<open>e = \<langle>\<langle>x, y\<rangle>, \<langle>a, b\<rangle>\<rangle>\<close>.\<close>

lemma JArr_eta [simp]:
  "e \<in> JArr C \<phi> \<Longrightarrow> \<langle>\<langle>pfst (pfst e), psnd (pfst e)\<rangle>, \<langle>pfst (psnd e), psnd (psnd e)\<rangle>\<rangle> = e"
  by (auto simp: mem_JArr)

lemma JArr_dom [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> pfst (pfst e) \<in> JOb \<phi>"
  by (auto simp: mem_JArr)

lemma JArr_cod [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> psnd (pfst e) \<in> JOb \<phi>"
  by (auto simp: mem_JArr)

lemma JArr_fst [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> pfst (psnd e) \<in> Arr (ix (asrc \<phi>))"
  by (auto simp: mem_JArr)

lemma JArr_fst_src [simp]:
  "e \<in> JArr C \<phi> \<Longrightarrow> src\<^bsub>ix (asrc \<phi>)\<^esub> (pfst (psnd e)) = pfst (pfst (pfst e))"
  by (auto simp: mem_JArr)

lemma JArr_fst_tgt [simp]:
  "e \<in> JArr C \<phi> \<Longrightarrow> tgt\<^bsub>ix (asrc \<phi>)\<^esub> (pfst (psnd e)) = pfst (psnd (pfst e))"
  by (auto simp: mem_JArr)

lemma JArr_snd [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> psnd (psnd e) \<in> Arr (ix (atgt \<phi>))"
  by (auto simp: mem_JArr)

lemma JArr_snd_src [simp]:
  "e \<in> JArr C \<phi> \<Longrightarrow> src\<^bsub>ix (atgt \<phi>)\<^esub> (psnd (psnd e)) = pfst (psnd (pfst (pfst e)))"
  by (auto simp: mem_JArr)

lemma JArr_snd_tgt [simp]:
  "e \<in> JArr C \<phi> \<Longrightarrow> tgt\<^bsub>ix (atgt \<phi>)\<^esub> (psnd (psnd e)) = pfst (psnd (psnd (pfst e)))"
  by (auto simp: mem_JArr)

lemma JArr_square:
  "e \<in> JArr C \<phi> \<Longrightarrow>
    dg (atgt \<phi>) \<cdot>\<^sub>a psnd (psnd e) \<circ>\<^bsub>C\<^esub> psnd (psnd (pfst (pfst e))) =
      psnd (psnd (psnd (pfst e))) \<circ>\<^bsub>C\<^esub> dg (asrc \<phi>) \<cdot>\<^sub>a pfst (psnd e)"
  by (auto simp: mem_JArr)

subsection \<open>Sethood and definability\<close>

lemma M_JOb [simp]: "M (JOb \<phi>)"
proof (rule M_subcls)
  show "M \<lbrace>y. \<exists>\<^sub>s j. j \<in> Ob (ix (asrc \<phi>)) \<and> y \<in> sng j \<times> body \<phi> \<cdot> j\<rbrace>"
    by (rule M_UN) simp_all
  show "JOb \<phi> \<subseteq> \<lbrace>y. \<exists>\<^sub>s j. j \<in> Ob (ix (asrc \<phi>)) \<and> y \<in> sng j \<times> body \<phi> \<cdot> j\<rbrace>"
    by (auto simp: mem_JOb)
qed

lemma M_JArr [simp]: "M (JArr C \<phi>)"
proof (rule M_subcls)
  show "M ((JOb \<phi> \<times> JOb \<phi>) \<times> (Arr (ix (asrc \<phi>)) \<times> Arr (ix (atgt \<phi>))))"
    by simp
  show "JArr C \<phi> \<subseteq> (JOb \<phi> \<times> JOb \<phi>) \<times> (Arr (ix (asrc \<phi>)) \<times> Arr (ix (atgt \<phi>)))"
    by (auto simp: mem_JArr)
qed

lemma M_Jid [simp]: "M (Jid \<phi> x)"
  by (simp add: Jid_def)

lemma M_Jcomp [simp]: "M (Jcomp \<phi> g h)"
  by (simp add: Jcomp_def)

lemma dfun_JOb [dfn_rules]: "dcls P \<Longrightarrow> dfun (\<lambda>x. JOb (P x))"
proof -
  assume "dcls P"
  then have "dcls (\<lambda>x. JOb (P x))"
    unfolding JOb_def by dfn
  then show ?thesis
    unfolding dfun_def by simp
qed

lemma dfun_JArr [dfn_rules]: "dcls T \<Longrightarrow> dcls P \<Longrightarrow> dfun (\<lambda>x. JArr (T x) (P x))"
proof -
  assume "dcls T" "dcls P"
  then have "dcls (\<lambda>x. JArr (T x) (P x))"
    unfolding JArr_def by dfn
  then show ?thesis
    unfolding dfun_def by simp
qed

lemma dfun_Jid [dfn_rules]: "dcls P \<Longrightarrow> dcls X \<Longrightarrow> dfun (\<lambda>x. Jid (P x) (X x))"
  unfolding Jid_def by dfn

lemma dfun_Jcomp [dfn_rules]: "dcls P \<Longrightarrow> dcls G \<Longrightarrow> dcls H \<Longrightarrow> dfun (\<lambda>x. Jcomp (P x) (G x) (H x))"
  unfolding Jcomp_def by dfn

lemma dfun_Jphi [dfn_rules]: "dcls T \<Longrightarrow> dcls P \<Longrightarrow> dfun (\<lambda>x. Jphi (T x) (P x))"
  unfolding Jphi_def by dfn

lemma dfun_qphi [dfn_rules]: "dcls T \<Longrightarrow> dcls P \<Longrightarrow> dfun (\<lambda>x. qphi (T x) (P x))"
  unfolding qphi_def by dfn

lemma dfun_piphi [dfn_rules]: "dcls T \<Longrightarrow> dcls P \<Longrightarrow> dfun (\<lambda>x. piphi (T x) (P x))"
  unfolding piphi_def by dfn

lemma dfun_Xphi [dfn_rules]: "dcls T \<Longrightarrow> dcls P \<Longrightarrow> dfun (\<lambda>x. Xphi (T x) (P x))"
  unfolding Xphi_def by dfn

lemma dfun_wphi [dfn_rules]: "dcls T \<Longrightarrow> dcls P \<Longrightarrow> dfun (\<lambda>x. wphi (T x) (P x))"
  unfolding wphi_def by dfn

lemma dfun_tphi [dfn_rules]: "dcls T \<Longrightarrow> dcls P \<Longrightarrow> dfun (\<lambda>x. tphi (T x) (P x))"
  unfolding tphi_def by dfn

subsection \<open>The structure of \<open>J\<^sub>\<phi>\<close> read off\<close>

lemma Jid_parts [simp]:
  "pfst (Jid \<phi> x) = \<langle>x, x\<rangle>"
  "psnd (Jid \<phi> x) = \<langle>id\<^bsub>ix (asrc \<phi>)\<^esub> (pfst x), id\<^bsub>ix (atgt \<phi>)\<^esub> (pfst (psnd x))\<rangle>"
  by (simp_all add: Jid_def)

lemma Jcomp_parts [simp]:
  "pfst (Jcomp \<phi> g h) = \<langle>pfst (pfst h), psnd (pfst g)\<rangle>"
  "psnd (Jcomp \<phi> g h) =
    \<langle>pfst (psnd g) \<circ>\<^bsub>ix (asrc \<phi>)\<^esub> pfst (psnd h), psnd (psnd g) \<circ>\<^bsub>ix (atgt \<phi>)\<^esub> psnd (psnd h)\<rangle>"
  by (simp_all add: Jcomp_def)

lemma M_Jphi [simp]: "M (Jphi C \<phi>)"
  by (simp add: Jphi_def)

lemma Ob_Jphi [simp]: "Ob (Jphi C \<phi>) = JOb \<phi>"
  by (simp add: Jphi_def)

lemma Arr_Jphi [simp]: "Arr (Jphi C \<phi>) = JArr C \<phi>"
  by (simp add: Jphi_def)

lemma src_Jphi [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> src\<^bsub>Jphi C \<phi>\<^esub> e = pfst (pfst e)"
  by (simp add: Jphi_def)

lemma tgt_Jphi [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> tgt\<^bsub>Jphi C \<phi>\<^esub> e = psnd (pfst e)"
  by (simp add: Jphi_def)

lemma id_Jphi [simp]: "x \<in> JOb \<phi> \<Longrightarrow> id\<^bsub>Jphi C \<phi>\<^esub> x = Jid \<phi> x"
  by (simp add: Jphi_def)

lemma comp_Jphi [simp]: "g \<in> JArr C \<phi> \<Longrightarrow> h \<in> JArr C \<phi> \<Longrightarrow> g \<circ>\<^bsub>Jphi C \<phi>\<^esub> h = Jcomp \<phi> g h"
  by (simp add: Jphi_def mem_M)

subsection \<open>The projections, the diagram and the two arrows read off\<close>

lemma M_qphi [simp]: "M (qphi C \<phi>)"
  by (simp add: qphi_def)

lemma M_piphi [simp]: "M (piphi C \<phi>)"
  by (simp add: piphi_def)

lemma qphi_obj [simp]: "x \<in> JOb \<phi> \<Longrightarrow> qphi C \<phi> \<cdot>\<^sub>o x = pfst x"
  by (simp add: qphi_def)

lemma qphi_arr [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> qphi C \<phi> \<cdot>\<^sub>a e = pfst (psnd e)"
  by (simp add: qphi_def)

lemma piphi_obj [simp]: "x \<in> JOb \<phi> \<Longrightarrow> piphi C \<phi> \<cdot>\<^sub>o x = pfst (psnd x)"
  by (simp add: piphi_def)

lemma piphi_arr [simp]: "e \<in> JArr C \<phi> \<Longrightarrow> piphi C \<phi> \<cdot>\<^sub>a e = psnd (psnd e)"
  by (simp add: piphi_def)

lemma M_Xphi [simp]: "M (Xphi C \<phi>)"
  by (simp add: Xphi_def)

lemma ix_Xphi [simp]: "ix (Xphi C \<phi>) = Jphi C \<phi>"
  by (simp add: Xphi_def)

lemma dg_Xphi [simp]: "dg (Xphi C \<phi>) = fcomp (Jphi C \<phi>) (dg (asrc \<phi>)) (qphi C \<phi>)"
  by (simp add: Xphi_def)

lemma asrc_wphi [simp]: "asrc (wphi C \<phi>) = Xphi C \<phi>"
  by (simp add: wphi_def)

lemma atgt_wphi [simp]: "atgt (wphi C \<phi>) = asrc \<phi>"
  by (simp add: wphi_def)

lemma afun_wphi [simp]: "afun (wphi C \<phi>) = qphi C \<phi>"
  by (simp add: wphi_def)

lemma anat_wphi [simp]:
  "anat (wphi C \<phi>) = (\<lambda>x\<in>Ob (Jphi C \<phi>). id\<^bsub>C\<^esub> (dg (asrc \<phi>) \<cdot>\<^sub>o (qphi C \<phi> \<cdot>\<^sub>o x)))"
  by (simp add: wphi_def)

lemma asrc_tphi [simp]: "asrc (tphi C \<phi>) = Xphi C \<phi>"
  by (simp add: tphi_def)

lemma atgt_tphi [simp]: "atgt (tphi C \<phi>) = atgt \<phi>"
  by (simp add: tphi_def)

lemma afun_tphi [simp]: "afun (tphi C \<phi>) = piphi C \<phi>"
  by (simp add: tphi_def)

lemma anat_tphi [simp]: "anat (tphi C \<phi>) = (\<lambda>x\<in>Ob (Jphi C \<phi>). psnd (psnd x))"
  by (simp add: tphi_def)

lemma anat_wphi_app [simp]:
  "x \<in> JOb \<phi> \<Longrightarrow> anat (wphi C \<phi>) \<cdot> x = id\<^bsub>C\<^esub> (dg (asrc \<phi>) \<cdot>\<^sub>o pfst x)"
  by simp

lemma anat_tphi_app [simp]: "x \<in> JOb \<phi> \<Longrightarrow> anat (tphi C \<phi>) \<cdot> x = psnd (psnd x)"
  by simp

subsection \<open>Over an arrow of \<open>PSh C\<close>\<close>

text \<open>
  From here on \<open>\<phi>\<close> is an arrow of \<open>PSh C\<close>, with \<open>C\<close> a locally small category. Then every
  object of \<open>J\<^sub>\<phi>\<close> is a triple \<open>\<langle>j, \<langle>k, f\<rangle>\<rangle>\<close> with \<open>f : F j \<rightarrow> G k\<close>.
\<close>

context
  fixes C \<phi> :: cls
  assumes C [simp]: "category C" and ls: "locally_small C" and phi [simp]: "\<phi> \<in> PArr C"
begin

lemma phi_src_functor: "is_functor (dg (asrc \<phi>)) (ix (asrc \<phi>)) C"
  by (rule DOb_functor) simp

lemma phi_tgt_functor: "is_functor (dg (atgt \<phi>)) (ix (atgt \<phi>)) C"
  by (rule DOb_functor) simp

lemma phi_src_category [simp]: "category (ix (asrc \<phi>))"
  by (rule PArr_category_src[OF phi])

lemma phi_tgt_category [simp]: "category (ix (atgt \<phi>))"
  by (rule PArr_category_tgt[OF phi])

lemma phi_src_id [simp]:
  "j \<in> Ob (ix (asrc \<phi>)) \<Longrightarrow> dg (asrc \<phi>) \<cdot>\<^sub>a id\<^bsub>ix (asrc \<phi>)\<^esub> j = id\<^bsub>C\<^esub> (dg (asrc \<phi>) \<cdot>\<^sub>o j)"
  by (rule functor_id[OF phi_src_functor])

lemma phi_tgt_id [simp]:
  "k \<in> Ob (ix (atgt \<phi>)) \<Longrightarrow> dg (atgt \<phi>) \<cdot>\<^sub>a id\<^bsub>ix (atgt \<phi>)\<^esub> k = id\<^bsub>C\<^esub> (dg (atgt \<phi>) \<cdot>\<^sub>o k)"
  by (rule functor_id[OF phi_tgt_functor])

lemma JObE:
  assumes "x \<in> JOb \<phi>"
  obtains j k f where "x = \<langle>j, \<langle>k, f\<rangle>\<rangle>" and "M j" and "M k" and "M f"
    and "j \<in> Ob (ix (asrc \<phi>))" and "\<langle>k, f\<rangle> \<in> body \<phi> \<cdot> j" and "k \<in> Ob (ix (atgt \<phi>))"
    and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j" and "tgt\<^bsub>C\<^esub> f = dg (atgt \<phi>) \<cdot>\<^sub>o k"
proof -
  obtain j v where "M j" "M v" and x: "x = \<langle>j, v\<rangle>" and j: "j \<in> Ob (ix (asrc \<phi>))"
    and v: "v \<in> body \<phi> \<cdot> j"
    using assms unfolding mem_JOb by blast
  obtain k f where "v = \<langle>k, f\<rangle>" "M k" "M f" "k \<in> Ob (ix (atgt \<phi>))" "f \<in> Arr C"
      "src\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> f = dg (atgt \<phi>) \<cdot>\<^sub>o k"
    using C ls phi j v by (rule PArr_body_memE)
  then show ?thesis
    using that x j v \<open>M j\<close> by blast
qed

lemma JOb_eta [simp]: "x \<in> JOb \<phi> \<Longrightarrow> \<langle>pfst x, \<langle>pfst (psnd x), psnd (psnd x)\<rangle>\<rangle> = x"
  by (erule JObE) simp

lemma JOb_body [simp]: "x \<in> JOb \<phi> \<Longrightarrow> \<langle>pfst (psnd x), psnd (psnd x)\<rangle> \<in> body \<phi> \<cdot> pfst x"
  by (erule JObE) simp

lemma JOb_k [simp]: "x \<in> JOb \<phi> \<Longrightarrow> pfst (psnd x) \<in> Ob (ix (atgt \<phi>))"
  by (erule JObE) simp

lemma JOb_f [simp]: "x \<in> JOb \<phi> \<Longrightarrow> psnd (psnd x) \<in> Arr C"
  by (erule JObE) simp

lemma JOb_f_src [simp]: "x \<in> JOb \<phi> \<Longrightarrow> src\<^bsub>C\<^esub> (psnd (psnd x)) = dg (asrc \<phi>) \<cdot>\<^sub>o pfst x"
  by (erule JObE) simp

lemma JOb_f_tgt [simp]: "x \<in> JOb \<phi> \<Longrightarrow> tgt\<^bsub>C\<^esub> (psnd (psnd x)) = dg (atgt \<phi>) \<cdot>\<^sub>o pfst (psnd x)"
  by (erule JObE) simp

subsection \<open>\<open>J\<^sub>\<phi>\<close> is a small category\<close>

lemma Jid_JArr [simp]: "x \<in> JOb \<phi> \<Longrightarrow> Jid \<phi> x \<in> JArr C \<phi>"
  unfolding Jid_def by (erule JObE) simp

lemma Jcomp_JArr [simp]:
  assumes g: "g \<in> JArr C \<phi>" and h: "h \<in> JArr C \<phi>" and gh: "pfst (pfst g) = psnd (pfst h)"
  shows "Jcomp \<phi> g h \<in> JArr C \<phi>"
proof -
  let ?F = "dg (asrc \<phi>)" and ?G = "dg (atgt \<phi>)"
  let ?x = "pfst (pfst h)" and ?y = "psnd (pfst h)" and ?z = "psnd (pfst g)"
  let ?a = "pfst (psnd h)" and ?b = "psnd (psnd h)" and ?a' = "pfst (psnd g)"
    and ?b' = "psnd (psnd g)"
  have sq1: "?G \<cdot>\<^sub>a ?b \<circ>\<^bsub>C\<^esub> psnd (psnd ?x) = psnd (psnd ?y) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a ?a"
    by (rule JArr_square[OF h])
  have sq2: "?G \<cdot>\<^sub>a ?b' \<circ>\<^bsub>C\<^esub> psnd (psnd ?y) = psnd (psnd ?z) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a ?a'"
    using JArr_square[OF g] gh by simp
  have "?G \<cdot>\<^sub>a (?b' \<circ>\<^bsub>ix (atgt \<phi>)\<^esub> ?b) \<circ>\<^bsub>C\<^esub> psnd (psnd ?x) =
      (?G \<cdot>\<^sub>a ?b' \<circ>\<^bsub>C\<^esub> ?G \<cdot>\<^sub>a ?b) \<circ>\<^bsub>C\<^esub> psnd (psnd ?x)"
    using functor_comp[OF phi_tgt_functor, of ?b ?b'] g h gh by simp
  also have "\<dots> = ?G \<cdot>\<^sub>a ?b' \<circ>\<^bsub>C\<^esub> (?G \<cdot>\<^sub>a ?b \<circ>\<^bsub>C\<^esub> psnd (psnd ?x))"
    by (rule cat_assoc[symmetric]) (use g h gh in simp_all)
  also have "\<dots> = ?G \<cdot>\<^sub>a ?b' \<circ>\<^bsub>C\<^esub> (psnd (psnd ?y) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a ?a)"
    by (simp only: sq1)
  also have "\<dots> = (?G \<cdot>\<^sub>a ?b' \<circ>\<^bsub>C\<^esub> psnd (psnd ?y)) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a ?a"
    by (rule cat_assoc) (use g h gh in simp_all)
  also have "\<dots> = (psnd (psnd ?z) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a ?a') \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a ?a"
    by (simp only: sq2)
  also have "\<dots> = psnd (psnd ?z) \<circ>\<^bsub>C\<^esub> (?F \<cdot>\<^sub>a ?a' \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a ?a)"
    by (rule cat_assoc[symmetric]) (use g h gh in simp_all)
  also have "\<dots> = psnd (psnd ?z) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a (?a' \<circ>\<^bsub>ix (asrc \<phi>)\<^esub> ?a)"
    using functor_comp[OF phi_src_functor, of ?a ?a'] g h gh by simp
  finally have sq: "?G \<cdot>\<^sub>a (?b' \<circ>\<^bsub>ix (atgt \<phi>)\<^esub> ?b) \<circ>\<^bsub>C\<^esub> psnd (psnd ?x) =
      psnd (psnd ?z) \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a (?a' \<circ>\<^bsub>ix (asrc \<phi>)\<^esub> ?a)" .
  show ?thesis
    unfolding Jcomp_def using g h gh sq by simp
qed

theorem Jphi_category: "category (Jphi C \<phi>)"
proof (rule categoryI)
  show "e \<circ>\<^bsub>Jphi C \<phi>\<^esub> id\<^bsub>Jphi C \<phi>\<^esub> (src\<^bsub>Jphi C \<phi>\<^esub> e) = e" if "e \<in> Arr (Jphi C \<phi>)" for e
    using that by simp (simp add: Jcomp_def)
  show "id\<^bsub>Jphi C \<phi>\<^esub> (tgt\<^bsub>Jphi C \<phi>\<^esub> e) \<circ>\<^bsub>Jphi C \<phi>\<^esub> e = e" if "e \<in> Arr (Jphi C \<phi>)" for e
    using that by simp (simp add: Jcomp_def)
  show "h \<circ>\<^bsub>Jphi C \<phi>\<^esub> (g \<circ>\<^bsub>Jphi C \<phi>\<^esub> f) = (h \<circ>\<^bsub>Jphi C \<phi>\<^esub> g) \<circ>\<^bsub>Jphi C \<phi>\<^esub> f"
    if "f \<in> Arr (Jphi C \<phi>)" "g \<in> Arr (Jphi C \<phi>)" "h \<in> Arr (Jphi C \<phi>)"
      "src\<^bsub>Jphi C \<phi>\<^esub> g = tgt\<^bsub>Jphi C \<phi>\<^esub> f" "src\<^bsub>Jphi C \<phi>\<^esub> h = tgt\<^bsub>Jphi C \<phi>\<^esub> g" for f g h
    using that by simp (simp add: Jcomp_def cat_assoc)
qed (simp_all add: mem_M)

subsection \<open>The projections are functors\<close>

theorem qphi_strict: "strict_functor (qphi C \<phi>) (Jphi C \<phi>) (ix (asrc \<phi>))"
proof (rule strict_functorI)
  show "is_functor (qphi C \<phi>) (Jphi C \<phi>) (ix (asrc \<phi>))"
    by (rule is_functorI) (simp_all add: mem_M)
  show "qphi C \<phi> = mkfun (\<lambda>x\<in>Ob (Jphi C \<phi>). qphi C \<phi> \<cdot>\<^sub>o x) (\<lambda>e\<in>Arr (Jphi C \<phi>). qphi C \<phi> \<cdot>\<^sub>a e)"
    by (simp cong: Lam_cong) (simp add: qphi_def)
qed

theorem piphi_strict: "strict_functor (piphi C \<phi>) (Jphi C \<phi>) (ix (atgt \<phi>))"
proof (rule strict_functorI)
  show "is_functor (piphi C \<phi>) (Jphi C \<phi>) (ix (atgt \<phi>))"
    by (rule is_functorI) (simp_all add: mem_M)
  show "piphi C \<phi> = mkfun (\<lambda>x\<in>Ob (Jphi C \<phi>). piphi C \<phi> \<cdot>\<^sub>o x) (\<lambda>e\<in>Arr (Jphi C \<phi>). piphi C \<phi> \<cdot>\<^sub>a e)"
    by (simp cong: Lam_cong) (simp add: piphi_def)
qed

lemma qphi_functor: "is_functor (qphi C \<phi>) (Jphi C \<phi>) (ix (asrc \<phi>))"
  by (rule strict_functor_functor[OF qphi_strict])

lemma piphi_functor: "is_functor (piphi C \<phi>) (Jphi C \<phi>) (ix (atgt \<phi>))"
  by (rule strict_functor_functor[OF piphi_strict])

subsection \<open>The projection \<open>q\<close> is final\<close>

text \<open>
  Over \<open>j\<close>, a vertex \<open>\<langle>x, u\<rangle>\<close> with \<open>x = \<langle>j', \<langle>k, f\<rangle>\<rangle>\<close> and \<open>u : j \<rightarrow> j'\<close> is joined by an edge to
  the vertex \<open>\<langle>\<langle>j, \<langle>k, f \<circ> F u\<rangle>\<rangle>, id j\<rangle>\<close> (the hub), through the arrow \<open>(u, id k)\<close> of \<open>J\<^sub>\<phi>\<close>. Two
  hubs \<open>\<langle>\<langle>j, w\<rangle>, id j\<rangle>\<close>, \<open>\<langle>\<langle>j, w'\<rangle>, id j\<rangle>\<close> are connected because \<open>w\<close> and \<open>w'\<close> are connected in
  the component \<open>\<phi> \<cdot> j\<close>: an edge \<open>c\<close> there gives the arrow \<open>(id j, c)\<close> of \<open>J\<^sub>\<phi>\<close>.
\<close>

lemma qphi_hub:
  assumes j: "j \<in> Ob (ix (asrc \<phi>))"
    and v: "v \<in> comma_verts (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j"
  obtains w where "w \<in> body \<phi> \<cdot> j"
    and "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j) v \<langle>\<langle>j, w\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle>"
    and "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j) \<langle>\<langle>j, w\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle> v"
proof -
  let ?J = "ix (asrc \<phi>)" and ?F = "dg (asrc \<phi>)"
  let ?E = "comma_edges ?J (Jphi C \<phi>) (qphi C \<phi>) j"
  obtain x u where vu: "v = \<langle>x, u\<rangle>" and x: "x \<in> Ob (Jphi C \<phi>)" and u: "u \<in> Arr ?J"
    "src\<^bsub>?J\<^esub> u = j" "tgt\<^bsub>?J\<^esub> u = qphi C \<phi> \<cdot>\<^sub>o x"
    using v by (rule comma_vertsE)
  have x': "x \<in> JOb \<phi>"
    using x by simp
  let ?k = "pfst (psnd x)" and ?f = "psnd (psnd x)"
  let ?w = "\<langle>?k, ?f \<circ>\<^bsub>C\<^esub> ?F \<cdot>\<^sub>a u\<rangle>"
  have kf: "?w \<in> body \<phi> \<cdot> j"
    using PArr_compat[OF phi u(1), of ?k ?f] x' u by simp
  let ?e = "\<langle>\<langle>\<langle>j, ?w\<rangle>, x\<rangle>, \<langle>u, id\<^bsub>ix (atgt \<phi>)\<^esub> ?k\<rangle>\<rangle>"
  have e: "?e \<in> JArr C \<phi>"
    using j kf x' u by (simp add: mem_M)
  have "\<langle>\<langle>src\<^bsub>Jphi C \<phi>\<^esub> ?e, id\<^bsub>?J\<^esub> j\<rangle>, \<langle>tgt\<^bsub>Jphi C \<phi>\<^esub> ?e, qphi C \<phi> \<cdot>\<^sub>a ?e \<circ>\<^bsub>?J\<^esub> id\<^bsub>?J\<^esub> j\<rangle>\<rangle> \<in> ?E"
    by (rule comma_edgesI) (use e j kf x' in \<open>simp_all add: mem_M\<close>)
  then have edge: "\<langle>\<langle>\<langle>j, ?w\<rangle>, id\<^bsub>?J\<^esub> j\<rangle>, v\<rangle> \<in> ?E"
    using e j kf u x' unfolding vu by (simp add: mem_M)
  show ?thesis
    by (rule that[OF kf conn_edge_rev[OF edge] conn_edge[OF edge]]) (use v in \<open>simp_all add: mem_M\<close>)
qed

lemma qphi_base_conn:
  assumes j: "j \<in> Ob (ix (asrc \<phi>))" and w: "w \<in> body \<phi> \<cdot> j" and w': "w' \<in> body \<phi> \<cdot> j"
  shows "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j)
    \<langle>\<langle>j, w\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle> \<langle>\<langle>j, w'\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle>"
proof -
  let ?J = "ix (asrc \<phi>)" and ?K = "ix (atgt \<phi>)" and ?F = "dg (asrc \<phi>)" and ?G = "dg (atgt \<phi>)"
  let ?E = "cgraph C (atgt \<phi>) (?F \<cdot>\<^sub>o j)"
  let ?E' = "comma_edges ?J (Jphi C \<phi>) (qphi C \<phi>) j"
  have ww': "conn ?E w w'"
    by (rule PArr_body_conn[OF C ls phi j w w'])
  have ME: "M ?E"
    using ls j by simp
  show ?thesis
  proof (rule conn_induct[OF ME mem_M[OF w] ww', where P = "\<lambda>v. conn ?E' \<langle>\<langle>j, w\<rangle>, id\<^bsub>?J\<^esub> j\<rangle> \<langle>\<langle>j, v\<rangle>, id\<^bsub>?J\<^esub> j\<rangle>"])
    show "dfn (\<lambda>v. conn ?E' \<langle>\<langle>j, w\<rangle>, id\<^bsub>?J\<^esub> j\<rangle> \<langle>\<langle>j, v\<rangle>, id\<^bsub>?J\<^esub> j\<rangle>)"
      by dfn
    show "conn ?E' \<langle>\<langle>j, w\<rangle>, id\<^bsub>?J\<^esub> j\<rangle> \<langle>\<langle>j, w\<rangle>, id\<^bsub>?J\<^esub> j\<rangle>"
      by simp
    fix a b
    assume "M a" "M b" and ab: "\<langle>a, b\<rangle> \<in> ?E" and wa: "conn ?E w a"
    have a: "a \<in> body \<phi> \<cdot> j"
      by (rule PArr_body_closed[OF C ls phi j w wa])
    have b: "b \<in> body \<phi> \<cdot> j"
      by (rule PArr_body_closed[OF C ls phi j w conn_trans[OF wa conn_edge[OF ab \<open>M a\<close> \<open>M b\<close>]]])
    obtain g c where av: "a = \<langle>src\<^bsub>?K\<^esub> c, g\<rangle>" and bv: "b = \<langle>tgt\<^bsub>?K\<^esub> c, ?G \<cdot>\<^sub>a c \<circ>\<^bsub>C\<^esub> g\<rangle>"
      and c: "c \<in> Arr ?K" and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = ?F \<cdot>\<^sub>o j" "tgt\<^bsub>C\<^esub> g = ?G \<cdot>\<^sub>o src\<^bsub>?K\<^esub> c"
      using ab \<open>M a\<close> \<open>M b\<close> by (rule comma_edge_pairE)
    let ?e = "\<langle>\<langle>\<langle>j, a\<rangle>, \<langle>j, b\<rangle>\<rangle>, \<langle>id\<^bsub>?J\<^esub> j, c\<rangle>\<rangle>"
    have e: "?e \<in> JArr C \<phi>"
      using j a b c g \<open>M a\<close> \<open>M b\<close> unfolding av bv by (simp add: mem_M)
    have "\<langle>\<langle>src\<^bsub>Jphi C \<phi>\<^esub> ?e, id\<^bsub>?J\<^esub> j\<rangle>, \<langle>tgt\<^bsub>Jphi C \<phi>\<^esub> ?e, qphi C \<phi> \<cdot>\<^sub>a ?e \<circ>\<^bsub>?J\<^esub> id\<^bsub>?J\<^esub> j\<rangle>\<rangle> \<in> ?E'"
      by (rule comma_edgesI) (use e j a \<open>M a\<close> in \<open>simp_all add: mem_M\<close>)
    then have edge: "\<langle>\<langle>\<langle>j, a\<rangle>, id\<^bsub>?J\<^esub> j\<rangle>, \<langle>\<langle>j, b\<rangle>, id\<^bsub>?J\<^esub> j\<rangle>\<rangle> \<in> ?E'"
      using e j c \<open>M a\<close> \<open>M b\<close> by (simp add: mem_M)
    show "conn ?E' \<langle>\<langle>j, w\<rangle>, id\<^bsub>?J\<^esub> j\<rangle> \<langle>\<langle>j, a\<rangle>, id\<^bsub>?J\<^esub> j\<rangle> \<longleftrightarrow> conn ?E' \<langle>\<langle>j, w\<rangle>, id\<^bsub>?J\<^esub> j\<rangle> \<langle>\<langle>j, b\<rangle>, id\<^bsub>?J\<^esub> j\<rangle>"
      using conn_trans conn_edge[OF edge M_opair M_opair] conn_edge_rev[OF edge M_opair M_opair]
      by blast
  qed
qed

theorem qphi_final: "final_functor (qphi C \<phi>) (Jphi C \<phi>) (ix (asrc \<phi>))"
proof (rule final_functorI)
  show "\<exists>\<^sub>s v. v \<in> comma_verts (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j"
    if j: "j \<in> Ob (ix (asrc \<phi>))" for j
  proof -
    obtain k f where kf: "\<langle>k, f\<rangle> \<in> body \<phi> \<cdot> j" and "M k" and "M f" and "k \<in> Ob (ix (atgt \<phi>))"
      and "f \<in> Arr C" and "src\<^bsub>C\<^esub> f = dg (asrc \<phi>) \<cdot>\<^sub>o j" and "tgt\<^bsub>C\<^esub> f = dg (atgt \<phi>) \<cdot>\<^sub>o k"
      using phi j by (rule PArr_body_ex)
    have "\<langle>\<langle>j, \<langle>k, f\<rangle>\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle> \<in> comma_verts (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j"
      using j kf by (simp add: mem_M)
    then show ?thesis
      using M_opair by blast
  qed
  show "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j) u v"
    if j: "j \<in> Ob (ix (asrc \<phi>))"
      and u: "u \<in> comma_verts (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j"
      and v: "v \<in> comma_verts (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j" for j u v
  proof -
    obtain w1 where w1: "w1 \<in> body \<phi> \<cdot> j"
      and c1: "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j) u \<langle>\<langle>j, w1\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle>"
      and "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j) \<langle>\<langle>j, w1\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle> u"
      using j u by (rule qphi_hub)
    obtain w2 where w2: "w2 \<in> body \<phi> \<cdot> j"
      and "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j) v \<langle>\<langle>j, w2\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle>"
      and c2: "conn (comma_edges (ix (asrc \<phi>)) (Jphi C \<phi>) (qphi C \<phi>) j) \<langle>\<langle>j, w2\<rangle>, id\<^bsub>ix (asrc \<phi>)\<^esub> j\<rangle> v"
      using j v by (rule qphi_hub)
    show ?thesis
      using conn_trans[OF c1 conn_trans[OF qphi_base_conn[OF j w1 w2] c2]] .
  qed
qed

subsection \<open>The diagram \<open>X\<^sub>\<phi>\<close> and the arrows \<open>w\<^sub>\<phi>\<close>, \<open>t\<^sub>\<phi>\<close>\<close>

theorem Xphi_DOb: "Xphi C \<phi> \<in> DOb C"
  unfolding Xphi_def
  by (rule DObI) (simp_all add: Jphi_category fcomp_functor[OF Jphi_category qphi_functor phi_src_functor])

theorem wphi_DArr: "wphi C \<phi> \<in> DArr C"
  unfolding wphi_def
  by (rule DArrI) (simp_all add: Xphi_DOb qphi_strict)

theorem wphi_W0: "wphi C \<phi> \<in> W0 C"
  by (rule W0I) (simp_all add: wphi_DArr qphi_final)

theorem tphi_DArr: "tphi C \<phi> \<in> DArr C"
  unfolding tphi_def
  by (rule DArrI) (simp_all add: Xphi_DOb piphi_strict JArr_square)

text \<open>Each object of \<open>J\<^sub>\<phi>\<close> is sent by \<open>t\<^sub>\<phi>\<close> to a representative of \<open>\<phi>\<close>.\<close>

theorem tphi_rep:
  "x \<in> Ob (Jphi C \<phi>) \<Longrightarrow> \<langle>piphi C \<phi> \<cdot>\<^sub>o x, anat (tphi C \<phi>) \<cdot> x\<rangle> \<in> body \<phi> \<cdot> (qphi C \<phi> \<cdot>\<^sub>o x)"
  by simp

text \<open>In \<open>PSh C\<close>, \<open>t\<^sub>\<phi>\<close> becomes \<open>\<phi>\<close> after \<open>w\<^sub>\<phi>\<close>.\<close>

theorem colim_tphi:
  "colim_functor C \<cdot>\<^sub>a tphi C \<phi> = Pcomp C \<phi> (colim_functor C \<cdot>\<^sub>a wphi C \<phi>)"
proof -
  have w: "wphi C \<phi> \<in> DArr C"
    by (rule wphi_DArr)
  have t: "tphi C \<phi> \<in> DArr C"
    by (rule tphi_DArr)
  have cw: "colim_functor C \<cdot>\<^sub>a wphi C \<phi> \<in> PArr C"
    using C ls w by (rule colim_functor_PArr)
  have ct: "colim_functor C \<cdot>\<^sub>a tphi C \<phi> \<in> PArr C"
    using C ls t by (rule colim_functor_PArr)
  have ab: "asrc \<phi> = atgt (colim_functor C \<cdot>\<^sub>a wphi C \<phi>)"
    using w by simp
  have pc: "Pcomp C \<phi> (colim_functor C \<cdot>\<^sub>a wphi C \<phi>) \<in> PArr C"
    by (rule Pcomp_PArr[OF C ls cw phi ab])
  show ?thesis
  proof (rule PArr_eqI[OF ct pc])
    show "asrc (colim_functor C \<cdot>\<^sub>a tphi C \<phi>) = asrc (Pcomp C \<phi> (colim_functor C \<cdot>\<^sub>a wphi C \<phi>))"
      using t w by simp
    show "atgt (colim_functor C \<cdot>\<^sub>a tphi C \<phi>) = atgt (Pcomp C \<phi> (colim_functor C \<cdot>\<^sub>a wphi C \<phi>))"
      using t by simp
    show "body (colim_functor C \<cdot>\<^sub>a tphi C \<phi>) \<cdot> x = body (Pcomp C \<phi> (colim_functor C \<cdot>\<^sub>a wphi C \<phi>)) \<cdot> x"
      if x: "x \<in> Ob (ix (asrc (colim_functor C \<cdot>\<^sub>a tphi C \<phi>)))" for x
    proof -
      have x': "x \<in> JOb \<phi>"
        using x t by simp
      have xw: "x \<in> Ob (ix (asrc (colim_functor C \<cdot>\<^sub>a wphi C \<phi>)))"
        using x' w by simp
      have kf: "\<langle>pfst x, id\<^bsub>C\<^esub> (dg (asrc \<phi>) \<cdot>\<^sub>o pfst x)\<rangle> \<in> body (colim_functor C \<cdot>\<^sub>a wphi C \<phi>) \<cdot> x"
        using ls w x' by simp
      have "body (Pcomp C \<phi> (colim_functor C \<cdot>\<^sub>a wphi C \<phi>)) \<cdot> x =
          cc (cgraph C (atgt \<phi>) (dg (asrc (colim_functor C \<cdot>\<^sub>a wphi C \<phi>)) \<cdot>\<^sub>o x))
            \<langle>pfst (psnd x), psnd (psnd x) \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (dg (asrc \<phi>) \<cdot>\<^sub>o pfst x)\<rangle>"
        by (rule Pcomp_body_eq[OF C ls cw phi ab xw kf JOb_body[OF x'] M_pfst M_idt M_pfst M_psnd])
      then show ?thesis
        using ls t w x' by simp
    qed
  qed
qed

end

end
