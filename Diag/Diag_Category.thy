section \<open>Small diagrams form a category\<close>

theory Diag_Category
  imports Diagrams Cat.Functor
begin

subsection \<open>Reading objects and arrows\<close>

text \<open>
  The projections are sets whatever their argument, and give back the components of a pair of
  sets. The second component of an arrow is a pair of sets automatically, so \<open>body\<close> needs no
  hypothesis.
\<close>

lemma M_ix [simp]: "M (ix X)" by (simp add: ix_def)
lemma M_dg [simp]: "M (dg X)" by (simp add: dg_def)
lemma M_asrc [simp]: "M (asrc a)" by (simp add: asrc_def)
lemma M_atgt [simp]: "M (atgt a)" by (simp add: atgt_def)
lemma M_body [simp]: "M (body a)" by (simp add: body_def)
lemma M_afun [simp]: "M (afun a)" by (simp add: afun_def)
lemma M_anat [simp]: "M (anat a)" by (simp add: anat_def)

lemma ix_pair [simp]: "M J \<Longrightarrow> M F \<Longrightarrow> ix \<langle>J, F\<rangle> = J"
  by (simp add: ix_def)

lemma dg_pair [simp]: "M J \<Longrightarrow> M F \<Longrightarrow> dg \<langle>J, F\<rangle> = F"
  by (simp add: dg_def)

lemma asrc_pair [simp]: "M X \<Longrightarrow> M Y \<Longrightarrow> M m \<Longrightarrow> asrc \<langle>\<langle>X, Y\<rangle>, m\<rangle> = X"
  by (simp add: asrc_def)

lemma atgt_pair [simp]: "M X \<Longrightarrow> M Y \<Longrightarrow> M m \<Longrightarrow> atgt \<langle>\<langle>X, Y\<rangle>, m\<rangle> = Y"
  by (simp add: atgt_def)

lemma body_pair [simp]: "M m \<Longrightarrow> body \<langle>\<langle>X, Y\<rangle>, m\<rangle> = m"
  by (simp add: body_def)

lemma afun_pair [simp]: "M p \<Longrightarrow> M \<alpha> \<Longrightarrow> afun \<langle>\<langle>X, Y\<rangle>, \<langle>p, \<alpha>\<rangle>\<rangle> = p"
  by (simp add: afun_def)

lemma anat_pair [simp]: "M p \<Longrightarrow> M \<alpha> \<Longrightarrow> anat \<langle>\<langle>X, Y\<rangle>, \<langle>p, \<alpha>\<rangle>\<rangle> = \<alpha>"
  by (simp add: anat_def)

subsection \<open>Objects\<close>

text \<open>An object is a pair of a small category and a functor from it to \<open>C\<close>.\<close>

lemma mem_DOb: "X \<in> DOb C \<longleftrightarrow> (\<exists>\<^sub>s J F. X = \<langle>J, F\<rangle> \<and> category J \<and> is_functor F J C)"
  by (auto simp: DOb_def)

lemma opair_mem_DOb [simp]:
  "M J \<Longrightarrow> M F \<Longrightarrow> \<langle>J, F\<rangle> \<in> DOb C \<longleftrightarrow> category J \<and> is_functor F J C"
  by (auto simp: mem_DOb)

lemma DObI: "M J \<Longrightarrow> M F \<Longrightarrow> category J \<Longrightarrow> is_functor F J C \<Longrightarrow> \<langle>J, F\<rangle> \<in> DOb C"
  by simp

lemma DObE:
  assumes "X \<in> DOb C"
  obtains J F where "M J" and "M F" and "X = \<langle>J, F\<rangle>" and "category J" and "is_functor F J C"
  using assms unfolding mem_DOb by blast

lemma DOb_M: "X \<in> DOb C \<Longrightarrow> M X"
  by (rule mem_M)

lemma DOb_eta: "X \<in> DOb C \<Longrightarrow> X = \<langle>ix X, dg X\<rangle>"
  by (erule DObE) simp

lemma DOb_category [simp]: "X \<in> DOb C \<Longrightarrow> category (ix X)"
  by (erule DObE) simp

lemma DOb_functor: "X \<in> DOb C \<Longrightarrow> is_functor (dg X) (ix X) C"
  by (erule DObE) simp

subsection \<open>Arrows\<close>

text \<open>
  An arrow \<open>\<langle>\<langle>X, Y\<rangle>, \<langle>p, \<alpha>\<rangle>\<rangle>\<close>: a canonical functor \<open>p : ix X \<rightarrow> ix Y\<close> and a transformation \<open>\<alpha>\<close>,
  equal to its own \<open>\<lambda>\<close>, from \<open>dg X\<close> to \<open>dg Y \<circ> p\<close>. \<open>DArrI\<close> builds one; \<open>DArrD\<close> reads every
  property back through the projections, and the lemmas after it name each part.

  \<open>DOb_functor\<close> and \<open>DArr_functor\<close> are not simp rules on purpose. The simplifier cannot use them
  to discharge the hypothesis \<open>is_functor F ?C D\<close> of \<open>functor_obj\<close> (its \<open>?C\<close> is unknown), and
  as simp rules they would rewrite such a hypothesis, given with \<open>using\<close>, to \<open>True\<close> and lose it.
  Pass them with \<open>using\<close>.
\<close>

lemma DArrI:
  assumes X: "X \<in> DOb C" and Y: "Y \<in> DOb C" and p: "strict_functor p (ix X) (ix Y)"
    and \<alpha>: "\<alpha> = (\<lambda>j\<in>Ob (ix X). \<alpha> \<cdot> j)"
    and arr: "\<And>j. j \<in> Ob (ix X) \<Longrightarrow> \<alpha> \<cdot> j \<in> Arr C"
    and src: "\<And>j. j \<in> Ob (ix X) \<Longrightarrow> src\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg X \<cdot>\<^sub>o j"
    and tgt: "\<And>j. j \<in> Ob (ix X) \<Longrightarrow> tgt\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg Y \<cdot>\<^sub>o (p \<cdot>\<^sub>o j)"
    and nat: "\<And>u. u \<in> Arr (ix X) \<Longrightarrow>
      \<alpha> \<cdot> tgt\<^bsub>ix X\<^esub> u \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u = dg Y \<cdot>\<^sub>a (p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> \<alpha> \<cdot> src\<^bsub>ix X\<^esub> u"
  shows "\<langle>\<langle>X, Y\<rangle>, \<langle>p, \<alpha>\<rangle>\<rangle> \<in> DArr C"
proof -
  have "M X" and "M Y"
    using X Y by (simp_all add: mem_M)
  have "M p"
    using M_ix p by (rule M_strict_functor)
  have "M (\<lambda>j\<in>Ob (ix X). \<alpha> \<cdot> j)"
    by simp
  then have "M \<alpha>"
    by (metis \<alpha>)
  show ?thesis
    unfolding DArr_def
    apply (rule CollI)
      apply dfn
     apply simp
    using X Y p \<alpha> arr src tgt nat \<open>M X\<close> \<open>M Y\<close> \<open>M p\<close> \<open>M \<alpha>\<close> by blast
qed

lemma DArr_unfold:
  assumes "a \<in> DArr C"
  shows "\<exists>\<^sub>s X Y p \<alpha>. a = \<langle>\<langle>X, Y\<rangle>, \<langle>p, \<alpha>\<rangle>\<rangle> \<and> X \<in> DOb C \<and> Y \<in> DOb C \<and>
      strict_functor p (ix X) (ix Y) \<and>
      \<alpha> = (\<lambda>j\<in>Ob (ix X). \<alpha> \<cdot> j) \<and>
      (\<forall>\<^sub>s j. j \<in> Ob (ix X) \<longrightarrow>
        \<alpha> \<cdot> j \<in> Arr C \<and> src\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg X \<cdot>\<^sub>o j \<and> tgt\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg Y \<cdot>\<^sub>o (p \<cdot>\<^sub>o j)) \<and>
      (\<forall>\<^sub>s u. u \<in> Arr (ix X) \<longrightarrow>
        \<alpha> \<cdot> tgt\<^bsub>ix X\<^esub> u \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u = dg Y \<cdot>\<^sub>a (p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> \<alpha> \<cdot> src\<^bsub>ix X\<^esub> u)"
  using assms unfolding DArr_def by (rule CollD) dfn

lemma DArrD:
  assumes "a \<in> DArr C"
  shows "a = \<langle>\<langle>asrc a, atgt a\<rangle>, \<langle>afun a, anat a\<rangle>\<rangle>"
    and "asrc a \<in> DOb C"
    and "atgt a \<in> DOb C"
    and "strict_functor (afun a) (ix (asrc a)) (ix (atgt a))"
    and "anat a = (\<lambda>j\<in>Ob (ix (asrc a)). anat a \<cdot> j)"
    and "\<And>j. j \<in> Ob (ix (asrc a)) \<Longrightarrow> anat a \<cdot> j \<in> Arr C"
    and "\<And>j. j \<in> Ob (ix (asrc a)) \<Longrightarrow> src\<^bsub>C\<^esub> (anat a \<cdot> j) = dg (asrc a) \<cdot>\<^sub>o j"
    and "\<And>j. j \<in> Ob (ix (asrc a)) \<Longrightarrow> tgt\<^bsub>C\<^esub> (anat a \<cdot> j) = dg (atgt a) \<cdot>\<^sub>o (afun a \<cdot>\<^sub>o j)"
    and "\<And>u. u \<in> Arr (ix (asrc a)) \<Longrightarrow>
      anat a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u =
        dg (atgt a) \<cdot>\<^sub>a (afun a \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> anat a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u"
proof -
  obtain X Y p \<alpha> where "M X" and "M Y" and "M p" and "M \<alpha>" and a: "a = \<langle>\<langle>X, Y\<rangle>, \<langle>p, \<alpha>\<rangle>\<rangle>"
    and X: "X \<in> DOb C" and Y: "Y \<in> DOb C" and p: "strict_functor p (ix X) (ix Y)"
    and \<alpha>: "\<alpha> = (\<lambda>j\<in>Ob (ix X). \<alpha> \<cdot> j)"
    and comp: "\<forall>\<^sub>s j. j \<in> Ob (ix X) \<longrightarrow>
      \<alpha> \<cdot> j \<in> Arr C \<and> src\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg X \<cdot>\<^sub>o j \<and> tgt\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg Y \<cdot>\<^sub>o (p \<cdot>\<^sub>o j)"
    and nat: "\<forall>\<^sub>s u. u \<in> Arr (ix X) \<longrightarrow>
      \<alpha> \<cdot> tgt\<^bsub>ix X\<^esub> u \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u = dg Y \<cdot>\<^sub>a (p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> \<alpha> \<cdot> src\<^bsub>ix X\<^esub> u"
    using DArr_unfold[OF assms] by blast
  have proj: "asrc a = X" "atgt a = Y" "afun a = p" "anat a = \<alpha>"
    using \<open>M X\<close> \<open>M Y\<close> \<open>M p\<close> \<open>M \<alpha>\<close> by (simp_all add: a)
  show "a = \<langle>\<langle>asrc a, atgt a\<rangle>, \<langle>afun a, anat a\<rangle>\<rangle>"
    unfolding proj by (fact a)
  show "asrc a \<in> DOb C"
    unfolding proj by (fact X)
  show "atgt a \<in> DOb C"
    unfolding proj by (fact Y)
  show "strict_functor (afun a) (ix (asrc a)) (ix (atgt a))"
    unfolding proj by (fact p)
  show "anat a = (\<lambda>j\<in>Ob (ix (asrc a)). anat a \<cdot> j)"
    unfolding proj by (fact \<alpha>)
  show "anat a \<cdot> j \<in> Arr C" if "j \<in> Ob (ix (asrc a))" for j
    using comp that mem_M unfolding proj by blast
  show "src\<^bsub>C\<^esub> (anat a \<cdot> j) = dg (asrc a) \<cdot>\<^sub>o j" if "j \<in> Ob (ix (asrc a))" for j
    using comp that mem_M unfolding proj by blast
  show "tgt\<^bsub>C\<^esub> (anat a \<cdot> j) = dg (atgt a) \<cdot>\<^sub>o (afun a \<cdot>\<^sub>o j)" if "j \<in> Ob (ix (asrc a))" for j
    using comp that mem_M unfolding proj by blast
  show "anat a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u =
      dg (atgt a) \<cdot>\<^sub>a (afun a \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> anat a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u"
    if "u \<in> Arr (ix (asrc a))" for u
    using nat that mem_M unfolding proj by blast
qed

lemma DArr_M: "a \<in> DArr C \<Longrightarrow> M a"
  by (rule mem_M)

lemma DArr_eta: "a \<in> DArr C \<Longrightarrow> a = \<langle>\<langle>asrc a, atgt a\<rangle>, \<langle>afun a, anat a\<rangle>\<rangle>"
  by (rule DArrD(1))

lemma DArr_asrc [simp]: "a \<in> DArr C \<Longrightarrow> asrc a \<in> DOb C"
  by (rule DArrD(2))

lemma DArr_atgt [simp]: "a \<in> DArr C \<Longrightarrow> atgt a \<in> DOb C"
  by (rule DArrD(3))

lemma DArr_category_src [simp]: "a \<in> DArr C \<Longrightarrow> category (ix (asrc a))"
  by (rule DOb_category) (rule DArrD(2))

lemma DArr_category_tgt [simp]: "a \<in> DArr C \<Longrightarrow> category (ix (atgt a))"
  by (rule DOb_category) (rule DArrD(3))

lemma DArr_strict: "a \<in> DArr C \<Longrightarrow> strict_functor (afun a) (ix (asrc a)) (ix (atgt a))"
  by (rule DArrD(4))

lemma DArr_functor: "a \<in> DArr C \<Longrightarrow> is_functor (afun a) (ix (asrc a)) (ix (atgt a))"
  by (rule strict_functor_functor) (rule DArrD(4))

lemma DArr_anat_Lam: "a \<in> DArr C \<Longrightarrow> anat a = (\<lambda>j\<in>Ob (ix (asrc a)). anat a \<cdot> j)"
  by (rule DArrD(5))

lemma DArr_anat_arr [simp]: "a \<in> DArr C \<Longrightarrow> j \<in> Ob (ix (asrc a)) \<Longrightarrow> anat a \<cdot> j \<in> Arr C"
  by (rule DArrD(6))

lemma DArr_anat_src [simp]:
  "a \<in> DArr C \<Longrightarrow> j \<in> Ob (ix (asrc a)) \<Longrightarrow> src\<^bsub>C\<^esub> (anat a \<cdot> j) = dg (asrc a) \<cdot>\<^sub>o j"
  by (rule DArrD(7))

lemma DArr_anat_tgt [simp]:
  "a \<in> DArr C \<Longrightarrow> j \<in> Ob (ix (asrc a)) \<Longrightarrow> tgt\<^bsub>C\<^esub> (anat a \<cdot> j) = dg (atgt a) \<cdot>\<^sub>o (afun a \<cdot>\<^sub>o j)"
  by (rule DArrD(8))

lemma DArr_anat_nat:
  "a \<in> DArr C \<Longrightarrow> u \<in> Arr (ix (asrc a)) \<Longrightarrow>
    anat a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u =
      dg (atgt a) \<cdot>\<^sub>a (afun a \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> anat a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u"
  by (rule DArrD(9))

lemma DArr_nat_trans:
  assumes "a \<in> DArr C"
  shows "nat_trans (anat a) (dg (asrc a)) (fcomp (ix (asrc a)) (dg (atgt a)) (afun a)) (ix (asrc a)) C"
  by (rule nat_transI) (use assms in \<open>simp_all add: DArr_anat_nat\<close>)

lemma DArr_eqI:
  assumes "a \<in> DArr C" and "b \<in> DArr C"
    and "asrc a = asrc b" and "atgt a = atgt b" and "afun a = afun b" and "anat a = anat b"
  shows "a = b"
proof -
  have "a = \<langle>\<langle>asrc a, atgt a\<rangle>, \<langle>afun a, anat a\<rangle>\<rangle>"
    using assms(1) by (rule DArr_eta)
  also have "\<dots> = \<langle>\<langle>asrc b, atgt b\<rangle>, \<langle>afun b, anat b\<rangle>\<rangle>"
    by (simp only: assms(3-6))
  also have "\<dots> = b"
    using assms(2) by (rule DArr_eta[symmetric])
  finally show ?thesis .
qed

subsection \<open>The category structure read off\<close>

text \<open>
  The six components of \<open>Diag C\<close>, with the four maps applied at members of their domains.
  Composition needs no composability hypothesis: \<open>Dcomp\<close> is applied to any pair of arrows.
\<close>

lemma M_Did [simp]: "M (Did C X)"
  by (simp add: Did_def)

lemma M_Dcomp [simp]: "M (Dcomp C b a)"
  by (simp add: Dcomp_def)

lemma Diag_Ob [simp]: "Ob (Diag C) = DOb C"
  by (simp add: Diag_def)

lemma Diag_Arr [simp]: "Arr (Diag C) = DArr C"
  by (simp add: Diag_def)

lemma Diag_src [simp]: "a \<in> DArr C \<Longrightarrow> src\<^bsub>Diag C\<^esub> a = asrc a"
  by (simp add: Diag_def)

lemma Diag_tgt [simp]: "a \<in> DArr C \<Longrightarrow> tgt\<^bsub>Diag C\<^esub> a = atgt a"
  by (simp add: Diag_def)

lemma Diag_id [simp]: "X \<in> DOb C \<Longrightarrow> id\<^bsub>Diag C\<^esub> X = Did C X"
  by (simp add: Diag_def)

lemma Diag_comp [simp]: "a \<in> DArr C \<Longrightarrow> b \<in> DArr C \<Longrightarrow> b \<circ>\<^bsub>Diag C\<^esub> a = Dcomp C b a"
  by (simp add: Diag_def mem_M)

subsection \<open>Identities\<close>

text \<open>
  The projections of \<open>Did C X\<close>; only source and target need \<open>X\<close> to be a set. The identity is an
  arrow when \<open>C\<close> is a category.
\<close>

lemma asrc_Did [simp]: "M X \<Longrightarrow> asrc (Did C X) = X"
  by (simp add: Did_def)

lemma atgt_Did [simp]: "M X \<Longrightarrow> atgt (Did C X) = X"
  by (simp add: Did_def)

lemma body_Did [simp]: "body (Did C X) = \<langle>idf (ix X), \<lambda>j\<in>Ob (ix X). id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j)\<rangle>"
  by (simp add: Did_def)

lemma afun_Did [simp]: "afun (Did C X) = idf (ix X)"
  by (simp add: afun_def)

lemma anat_Did [simp]: "anat (Did C X) = (\<lambda>j\<in>Ob (ix X). id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j))"
  by (simp add: anat_def)

lemma Did_DArr [simp]:
  assumes "category C" and "X \<in> DOb C"
  shows "Did C X \<in> DArr C"
  unfolding Did_def
proof (rule DArrI)
  show "strict_functor (idf (ix X)) (ix X) (ix X)"
    using assms(2) by (simp add: idf_strict)
qed (use assms DOb_functor[OF assms(2)] DOb_category[OF assms(2)] in simp_all)

subsection \<open>Composites\<close>

text \<open>
  The projections of \<open>Dcomp C b a\<close> hold for all \<open>a\<close> and \<open>b\<close>. The composite of composable arrows
  is an arrow; its naturality square is the two squares of \<open>a\<close> and \<open>b\<close> pasted, by associativity.
\<close>

lemma asrc_Dcomp [simp]: "asrc (Dcomp C b a) = asrc a"
  by (simp add: Dcomp_def)

lemma atgt_Dcomp [simp]: "atgt (Dcomp C b a) = atgt b"
  by (simp add: Dcomp_def)

lemma body_Dcomp [simp]:
  "body (Dcomp C b a) =
    \<langle>fcomp (ix (asrc a)) (afun b) (afun a),
      \<lambda>j\<in>Ob (ix (asrc a)). anat b \<cdot> (afun a \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> anat a \<cdot> j\<rangle>"
  by (simp add: Dcomp_def)

lemma afun_Dcomp [simp]: "afun (Dcomp C b a) = fcomp (ix (asrc a)) (afun b) (afun a)"
  by (simp add: afun_def)

lemma anat_Dcomp [simp]:
  "anat (Dcomp C b a) = (\<lambda>j\<in>Ob (ix (asrc a)). anat b \<cdot> (afun a \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> anat a \<cdot> j)"
  by (simp add: anat_def)

lemma Dcomp_DArr [simp]:
  assumes C: "category C" and a: "a \<in> DArr C" and b: "b \<in> DArr C" and ab: "asrc b = atgt a"
  shows "Dcomp C b a \<in> DArr C"
proof -
  let ?X = "asrc a" and ?Y = "atgt a" and ?Z = "atgt b"
  let ?p = "afun a" and ?q = "afun b" and ?\<alpha> = "anat a" and ?\<beta> = "anat b"
  have X: "?X \<in> DOb C" and Y: "?Y \<in> DOb C" and Z: "?Z \<in> DOb C"
    using a b by simp_all
  have FX: "is_functor (dg ?X) (ix ?X) C" and FY: "is_functor (dg ?Y) (ix ?Y) C"
    and FZ: "is_functor (dg ?Z) (ix ?Z) C"
    using X Y Z by (simp_all add: DOb_functor)
  have p: "is_functor ?p (ix ?X) (ix ?Y)"
    using a by (rule DArr_functor)
  have q: "is_functor ?q (ix ?Y) (ix ?Z)"
    using DArr_functor[OF b] ab by simp
  have \<beta>_arr: "?\<beta> \<cdot> k \<in> Arr C" and \<beta>_src: "src\<^bsub>C\<^esub> (?\<beta> \<cdot> k) = dg ?Y \<cdot>\<^sub>o k"
    and \<beta>_tgt: "tgt\<^bsub>C\<^esub> (?\<beta> \<cdot> k) = dg ?Z \<cdot>\<^sub>o (?q \<cdot>\<^sub>o k)" if "k \<in> Ob (ix ?Y)" for k
    using b that ab by simp_all
  have \<beta>_nat: "?\<beta> \<cdot> tgt\<^bsub>ix ?Y\<^esub> v \<circ>\<^bsub>C\<^esub> dg ?Y \<cdot>\<^sub>a v = dg ?Z \<cdot>\<^sub>a (?q \<cdot>\<^sub>a v) \<circ>\<^bsub>C\<^esub> ?\<beta> \<cdot> src\<^bsub>ix ?Y\<^esub> v"
    if "v \<in> Arr (ix ?Y)" for v
    using DArr_anat_nat[OF b] that ab by simp
  have nat: "(?\<beta> \<cdot> (?p \<cdot>\<^sub>o tgt\<^bsub>ix ?X\<^esub> u) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> tgt\<^bsub>ix ?X\<^esub> u) \<circ>\<^bsub>C\<^esub> dg ?X \<cdot>\<^sub>a u =
      dg ?Z \<cdot>\<^sub>a (?q \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u)) \<circ>\<^bsub>C\<^esub> (?\<beta> \<cdot> (?p \<cdot>\<^sub>o src\<^bsub>ix ?X\<^esub> u) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> src\<^bsub>ix ?X\<^esub> u)"
    if u: "u \<in> Arr (ix ?X)" for u
  proof -
    let ?s = "src\<^bsub>ix ?X\<^esub> u" and ?t = "tgt\<^bsub>ix ?X\<^esub> u"
    have cX: "category (ix ?X)"
      using a by simp
    have st: "?s \<in> Ob (ix ?X)" "?t \<in> Ob (ix ?X)"
      using cX u by simp_all
    have pu: "?p \<cdot>\<^sub>a u \<in> Arr (ix ?Y)"
      using p u by simp
    note facts = C a st pu \<beta>_arr \<beta>_src \<beta>_tgt p q u FX FY FZ
    have "(?\<beta> \<cdot> (?p \<cdot>\<^sub>o ?t) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?t) \<circ>\<^bsub>C\<^esub> dg ?X \<cdot>\<^sub>a u =
        ?\<beta> \<cdot> (?p \<cdot>\<^sub>o ?t) \<circ>\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?t \<circ>\<^bsub>C\<^esub> dg ?X \<cdot>\<^sub>a u)"
      by (rule cat_assoc[symmetric]) (use facts in simp_all)
    also have "\<dots> = ?\<beta> \<cdot> (?p \<cdot>\<^sub>o ?t) \<circ>\<^bsub>C\<^esub> (dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s)"
      using DArr_anat_nat[OF a u] by simp
    also have "\<dots> = (?\<beta> \<cdot> (?p \<cdot>\<^sub>o ?t) \<circ>\<^bsub>C\<^esub> dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u)) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s"
      by (rule cat_assoc) (use facts in simp_all)
    also have "\<dots> = (dg ?Z \<cdot>\<^sub>a (?q \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u)) \<circ>\<^bsub>C\<^esub> ?\<beta> \<cdot> (?p \<cdot>\<^sub>o ?s)) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s"
      using \<beta>_nat[OF pu] p u by simp
    also have "\<dots> = dg ?Z \<cdot>\<^sub>a (?q \<cdot>\<^sub>a (?p \<cdot>\<^sub>a u)) \<circ>\<^bsub>C\<^esub> (?\<beta> \<cdot> (?p \<cdot>\<^sub>o ?s) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s)"
      by (rule cat_assoc[symmetric]) (use facts in simp_all)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding Dcomp_def
  proof (rule DArrI)
    show "strict_functor (fcomp (ix ?X) ?q ?p) (ix ?X) (ix ?Z)"
      using a p q by (simp add: fcomp_strict)
  qed (use C a X Z FX p q \<beta>_arr \<beta>_src \<beta>_tgt nat in simp_all)
qed

subsection \<open>Unit and associativity laws\<close>

text \<open>
  The laws hold as equalities of classes because the functor part of an arrow is canonical
  (\<open>fcomp_idf_left\<close>, \<open>fcomp_idf_right\<close>) and the transformation part equals its own \<open>\<lambda>\<close>.
\<close>

lemma Dcomp_Did_right:
  assumes C: "category C" and a: "a \<in> DArr C"
  shows "Dcomp C a (Did C (asrc a)) = a"
proof -
  have "Dcomp C a (Did C (asrc a)) =
      \<langle>\<langle>asrc a, atgt a\<rangle>, \<langle>afun a, \<lambda>j\<in>Ob (ix (asrc a)). anat a \<cdot> j\<rangle>\<rangle>"
    unfolding Dcomp_def[of C a] using C a
    by (simp add: fcomp_idf_right[OF DArr_strict[OF a]])
  also have "\<dots> = a"
    unfolding DArr_anat_Lam[OF a, symmetric] by (rule DArr_eta[OF a, symmetric])
  finally show ?thesis .
qed

lemma Dcomp_Did_left:
  assumes C: "category C" and a: "a \<in> DArr C"
  shows "Dcomp C (Did C (atgt a)) a = a"
proof -
  have "Dcomp C (Did C (atgt a)) a =
      \<langle>\<langle>asrc a, atgt a\<rangle>, \<langle>afun a, \<lambda>j\<in>Ob (ix (asrc a)). anat a \<cdot> j\<rangle>\<rangle>"
    unfolding Dcomp_def[of C _ a] using C a DArr_functor[OF a]
    by (simp add: fcomp_idf_left[OF DArr_strict[OF a]])
  also have "\<dots> = a"
    unfolding DArr_anat_Lam[OF a, symmetric] by (rule DArr_eta[OF a, symmetric])
  finally show ?thesis .
qed

lemma Dcomp_assoc:
  assumes C: "category C" and f: "f \<in> DArr C" and g: "g \<in> DArr C" and h: "h \<in> DArr C"
    and fg: "asrc g = atgt f" and gh: "asrc h = atgt g"
  shows "Dcomp C h (Dcomp C g f) = Dcomp C (Dcomp C h g) f"
proof -
  have Ff: "is_functor (afun f) (ix (asrc f)) (ix (atgt f))"
    using f by (rule DArr_functor)
  have Fg: "is_functor (afun g) (ix (atgt f)) (ix (atgt g))"
    using DArr_functor[OF g] fg by simp
  have fa: "fcomp (ix (asrc f)) (afun h) (fcomp (ix (asrc f)) (afun g) (afun f)) =
      fcomp (ix (asrc f)) (fcomp (ix (atgt f)) (afun h) (afun g)) (afun f)"
    using Ff by (rule fcomp_assoc)
  show ?thesis
    unfolding Dcomp_def[of C h "Dcomp C g f"] Dcomp_def[of C "Dcomp C h g" f]
    using C f g h fg gh Ff Fg by (simp add: fa cat_assoc)
qed

subsection \<open>The theorem\<close>

theorem Diag_category:
  assumes "category C"
  shows "category (Diag C)"
  by (rule categoryI)
    (use assms in \<open>simp_all add: mem_M Dcomp_Did_left Dcomp_Did_right Dcomp_assoc\<close>)

end
