section \<open>Every morphism of presheaves is a span of diagrams\<close>

theory Spans
  imports Elements Colim_Functor
begin

text \<open>
  Every morphism \<open>\<phi>\<close> of presheaves becomes a morphism of diagrams after a final reindexing of
  its source: the span through the category \<open>J\<^sub>\<phi>\<close> of all representatives of \<open>\<phi>\<close>.
\<close>

theorem colim_has_spans:
  assumes "category C" and "locally_small C"
  shows "has_spans (colim_functor C) (W0 C) (Diag C) (PSh C)"
  unfolding has_spans_def
proof (intro allI impI)
  note C = assms(1) and ls = assms(2)
  fix \<phi>
  assume "M \<phi>" and "\<phi> \<in> Arr (PSh C)"
  then have \<phi>: "\<phi> \<in> PArr C"
    by simp
  have q: "wphi C \<phi> \<in> W0 C"
    by (rule wphi_W0[OF C ls \<phi>])
  have qD: "wphi C \<phi> \<in> DArr C"
    by (rule wphi_DArr[OF C ls \<phi>])
  have t: "tphi C \<phi> \<in> DArr C"
    by (rule tphi_DArr[OF C ls \<phi>])
  have Aq: "colim_functor C \<cdot>\<^sub>a wphi C \<phi> \<in> PArr C"
    by (rule colim_functor_PArr[OF C ls qD])
  have eq: "colim_functor C \<cdot>\<^sub>a tphi C \<phi> = Pcomp C \<phi> (colim_functor C \<cdot>\<^sub>a wphi C \<phi>)"
    by (rule colim_tphi[OF C ls \<phi>])
  have "wphi C \<phi> \<in> W0 C \<and> tphi C \<phi> \<in> Arr (Diag C) \<and>
      src\<^bsub>Diag C\<^esub> (tphi C \<phi>) = src\<^bsub>Diag C\<^esub> (wphi C \<phi>) \<and> tgt\<^bsub>Diag C\<^esub> (wphi C \<phi>) = src\<^bsub>PSh C\<^esub> \<phi> \<and>
      tgt\<^bsub>Diag C\<^esub> (tphi C \<phi>) = tgt\<^bsub>PSh C\<^esub> \<phi> \<and>
      colim_functor C \<cdot>\<^sub>a tphi C \<phi> = \<phi> \<circ>\<^bsub>PSh C\<^esub> colim_functor C \<cdot>\<^sub>a wphi C \<phi>"
    using q qD t \<phi> Aq eq by simp
  then show "\<exists>\<^sub>s q t. q \<in> W0 C \<and> t \<in> Arr (Diag C) \<and> src\<^bsub>Diag C\<^esub> t = src\<^bsub>Diag C\<^esub> q \<and>
      tgt\<^bsub>Diag C\<^esub> q = src\<^bsub>PSh C\<^esub> \<phi> \<and> tgt\<^bsub>Diag C\<^esub> t = tgt\<^bsub>PSh C\<^esub> \<phi> \<and>
      colim_functor C \<cdot>\<^sub>a t = \<phi> \<circ>\<^bsub>PSh C\<^esub> colim_functor C \<cdot>\<^sub>a q"
    using mem_M[OF q] mem_M[OF t] by blast
qed

text \<open>
  Two morphisms of diagrams with the same image both factor through \<open>J\<^sub>\<phi>\<close> for their common
  image \<open>\<phi>\<close>, by two sections of the same final reindexing.
\<close>

subsection \<open>The section of \<open>w\<^sub>\<phi>\<close> through a morphism of diagrams\<close>

text \<open>
  For a morphism \<open>a = (p, \<alpha>) : \<langle>J, F\<rangle> \<rightarrow> \<langle>K, G\<rangle>\<close> of diagrams with image \<open>\<phi>\<close>, the functor
  \<open>s : J \<rightarrow> J\<^sub>\<phi>\<close> sends \<open>j\<close> to \<open>\<langle>j, \<langle>p j, \<alpha> j\<rangle>\<rangle>\<close> and \<open>u\<close> to \<open>\<langle>u, p u\<rangle>\<close>; with identity components it is a
  morphism \<open>s\<^sub>a : \<langle>J, F\<rangle> \<rightarrow> X\<^sub>\<phi>\<close>, a section of \<open>w\<^sub>\<phi>\<close> with \<open>t\<^sub>\<phi> \<circ> s\<^sub>a = a\<close>. The functor does not depend on
  \<open>\<phi>\<close>; the morphism names \<open>\<phi>\<close> for its target.
\<close>

definition sphi_fun :: "cls \<Rightarrow> cls"
  where "sphi_fun a = mkfun
    (\<lambda>j\<in>Ob (ix (asrc a)). \<langle>j, \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle>\<rangle>)
    (\<lambda>u\<in>Arr (ix (asrc a)).
      \<langle>\<langle>\<langle>src\<^bsub>ix (asrc a)\<^esub> u, \<langle>afun a \<cdot>\<^sub>o src\<^bsub>ix (asrc a)\<^esub> u, anat a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u\<rangle>\<rangle>,
        \<langle>tgt\<^bsub>ix (asrc a)\<^esub> u, \<langle>afun a \<cdot>\<^sub>o tgt\<^bsub>ix (asrc a)\<^esub> u, anat a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u\<rangle>\<rangle>\<rangle>,
       \<langle>u, afun a \<cdot>\<^sub>a u\<rangle>\<rangle>)"

definition sphi :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "sphi C \<phi> a =
    \<langle>\<langle>asrc a, Xphi C \<phi>\<rangle>, \<langle>sphi_fun a, \<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)\<rangle>\<rangle>"

lemma sphi_fun_obj [simp]:
  "j \<in> Ob (ix (asrc a)) \<Longrightarrow> sphi_fun a \<cdot>\<^sub>o j = \<langle>j, \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle>\<rangle>"
  by (simp add: sphi_fun_def)

lemma sphi_fun_arr [simp]:
  "u \<in> Arr (ix (asrc a)) \<Longrightarrow> sphi_fun a \<cdot>\<^sub>a u =
    \<langle>\<langle>\<langle>src\<^bsub>ix (asrc a)\<^esub> u, \<langle>afun a \<cdot>\<^sub>o src\<^bsub>ix (asrc a)\<^esub> u, anat a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u\<rangle>\<rangle>,
      \<langle>tgt\<^bsub>ix (asrc a)\<^esub> u, \<langle>afun a \<cdot>\<^sub>o tgt\<^bsub>ix (asrc a)\<^esub> u, anat a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u\<rangle>\<rangle>\<rangle>,
     \<langle>u, afun a \<cdot>\<^sub>a u\<rangle>\<rangle>"
  by (simp add: sphi_fun_def)

lemma M_sphi_fun [simp]: "M (sphi_fun a)"
  by (simp add: sphi_fun_def)

lemma asrc_sphi [simp]: "asrc (sphi C \<phi> a) = asrc a"
  by (simp add: sphi_def)

lemma atgt_sphi [simp]: "atgt (sphi C \<phi> a) = Xphi C \<phi>"
  by (simp add: sphi_def)

lemma afun_sphi [simp]: "afun (sphi C \<phi> a) = sphi_fun a"
  by (simp add: sphi_def)

lemma anat_sphi [simp]: "anat (sphi C \<phi> a) = (\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j))"
  by (simp add: sphi_def)

context
  fixes C a \<phi>
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> DArr C"
    and \<phi>a: "colim_functor C \<cdot>\<^sub>a a = \<phi>"
begin

private lemma \<phi>P: "\<phi> \<in> PArr C"
  using colim_functor_PArr[OF C ls a] unfolding \<phi>a .

private lemma \<phi>s: "asrc \<phi> = asrc a"
  using asrc_colim_functor[OF a] unfolding \<phi>a .

private lemma \<phi>t: "atgt \<phi> = atgt a"
  using atgt_colim_functor[OF a] unfolding \<phi>a .

private lemma cJ: "category (ix (asrc a))"
  using a by simp

private lemma X: "asrc a \<in> DOb C"
  using a by simp

private lemma pF: "is_functor (afun a) (ix (asrc a)) (ix (atgt a))"
  using a by (rule DArr_functor)

text \<open>\<open>\<langle>p j, \<alpha> j\<rangle>\<close> is in the component \<open>\<phi> \<cdot> j\<close>, so \<open>s j\<close> is an object of \<open>J\<^sub>\<phi>\<close>; naturality of \<open>\<alpha>\<close> makes \<open>s u\<close> an arrow.\<close>

lemma sphi_obj_JOb:
  assumes j: "j \<in> Ob (ix (asrc a))"
  shows "\<langle>j, \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle>\<rangle> \<in> JOb \<phi>"
proof -
  have "body \<phi> \<cdot> j = cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle>"
    using colim_functor_body_app[OF C ls a j] unfolding \<phi>a .
  then have "\<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle> \<in> body \<phi> \<cdot> j"
    by simp
  then show ?thesis
    using j \<phi>s by (simp add: mem_M)
qed

lemma sphi_arr_JArr:
  assumes u: "u \<in> Arr (ix (asrc a))"
  shows "\<langle>\<langle>\<langle>src\<^bsub>ix (asrc a)\<^esub> u, \<langle>afun a \<cdot>\<^sub>o src\<^bsub>ix (asrc a)\<^esub> u, anat a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u\<rangle>\<rangle>,
      \<langle>tgt\<^bsub>ix (asrc a)\<^esub> u, \<langle>afun a \<cdot>\<^sub>o tgt\<^bsub>ix (asrc a)\<^esub> u, anat a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u\<rangle>\<rangle>\<rangle>,
     \<langle>u, afun a \<cdot>\<^sub>a u\<rangle>\<rangle> \<in> JArr C \<phi>"
proof -
  have s: "src\<^bsub>ix (asrc a)\<^esub> u \<in> Ob (ix (asrc a))" and t: "tgt\<^bsub>ix (asrc a)\<^esub> u \<in> Ob (ix (asrc a))"
    using cJ u by simp_all
  have nat: "dg (atgt a) \<cdot>\<^sub>a (afun a \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> anat a \<cdot> src\<^bsub>ix (asrc a)\<^esub> u =
      anat a \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u"
    using DArr_anat_nat[OF a u] by simp
  show ?thesis
    using u pF \<phi>s \<phi>t sphi_obj_JOb[OF s] sphi_obj_JOb[OF t] nat by (simp add: mem_M)
qed

text \<open>The functor \<open>s : J \<rightarrow> J\<^sub>\<phi>\<close>.\<close>

lemma sphi_fun_functor: "is_functor (sphi_fun a) (ix (asrc a)) (Jphi C \<phi>)"
proof (rule is_functorI)
  show "sphi_fun a \<cdot>\<^sub>o j \<in> Ob (Jphi C \<phi>)" if j: "j \<in> Ob (ix (asrc a))" for j
    using sphi_obj_JOb[OF j] j by simp
  show "sphi_fun a \<cdot>\<^sub>a u \<in> Arr (Jphi C \<phi>)" if u: "u \<in> Arr (ix (asrc a))" for u
    using sphi_arr_JArr[OF u] u by simp
  show "src\<^bsub>Jphi C \<phi>\<^esub> (sphi_fun a \<cdot>\<^sub>a u) = sphi_fun a \<cdot>\<^sub>o src\<^bsub>ix (asrc a)\<^esub> u"
    if u: "u \<in> Arr (ix (asrc a))" for u
    using sphi_arr_JArr[OF u] u cJ by (simp add: mem_M)
  show "tgt\<^bsub>Jphi C \<phi>\<^esub> (sphi_fun a \<cdot>\<^sub>a u) = sphi_fun a \<cdot>\<^sub>o tgt\<^bsub>ix (asrc a)\<^esub> u"
    if u: "u \<in> Arr (ix (asrc a))" for u
    using sphi_arr_JArr[OF u] u cJ by (simp add: mem_M)
  show "sphi_fun a \<cdot>\<^sub>a id\<^bsub>ix (asrc a)\<^esub> j = id\<^bsub>Jphi C \<phi>\<^esub> (sphi_fun a \<cdot>\<^sub>o j)"
    if j: "j \<in> Ob (ix (asrc a))" for j
    using j cJ pF \<phi>s \<phi>t sphi_obj_JOb[OF j] by (simp add: Jid_def mem_M)
  show "sphi_fun a \<cdot>\<^sub>a (g \<circ>\<^bsub>ix (asrc a)\<^esub> f) = sphi_fun a \<cdot>\<^sub>a g \<circ>\<^bsub>Jphi C \<phi>\<^esub> sphi_fun a \<cdot>\<^sub>a f"
    if f: "f \<in> Arr (ix (asrc a))" and g: "g \<in> Arr (ix (asrc a))"
      and gf: "src\<^bsub>ix (asrc a)\<^esub> g = tgt\<^bsub>ix (asrc a)\<^esub> f" for f g
    using f g gf cJ \<phi>s \<phi>t sphi_arr_JArr[OF f] sphi_arr_JArr[OF g] functor_comp[OF pF f g gf]
    by (simp add: Jcomp_def mem_M)
qed

lemma sphi_fun_strict: "strict_functor (sphi_fun a) (ix (asrc a)) (Jphi C \<phi>)"
proof (rule strict_functorI[OF sphi_fun_functor])
  show "sphi_fun a =
      mkfun (\<lambda>x\<in>Ob (ix (asrc a)). sphi_fun a \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr (ix (asrc a)). sphi_fun a \<cdot>\<^sub>a f)"
    by (simp cong: Lam_cong) (simp add: sphi_fun_def)
qed

text \<open>The morphism \<open>s\<^sub>a : \<langle>J, F\<rangle> \<rightarrow> X\<^sub>\<phi>\<close>.\<close>

lemma sphi_DArr: "sphi C \<phi> a \<in> DArr C"
  unfolding sphi_def
proof (rule DArrI)
  show "asrc a \<in> DOb C"
    by (rule X)
  show "Xphi C \<phi> \<in> DOb C"
    by (rule Xphi_DOb[OF C ls \<phi>P])
  show "strict_functor (sphi_fun a) (ix (asrc a)) (ix (Xphi C \<phi>))"
    using sphi_fun_strict by simp
  show "(\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)) =
      (\<lambda>j\<in>Ob (ix (asrc a)). (\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)) \<cdot> j)"
    by (rule Lam_eqI) simp
  show "(\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)) \<cdot> j \<in> Arr C"
    if j: "j \<in> Ob (ix (asrc a))" for j
    using C X j by simp
  show "src\<^bsub>C\<^esub> ((\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)) \<cdot> j) = dg (asrc a) \<cdot>\<^sub>o j"
    if j: "j \<in> Ob (ix (asrc a))" for j
    using C X j by simp
  show "tgt\<^bsub>C\<^esub> ((\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)) \<cdot> j) =
      dg (Xphi C \<phi>) \<cdot>\<^sub>o (sphi_fun a \<cdot>\<^sub>o j)"
    if j: "j \<in> Ob (ix (asrc a))" for j
    using C X j \<phi>s sphi_obj_JOb[OF j] by (simp add: mem_M)
  show "(\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)) \<cdot> tgt\<^bsub>ix (asrc a)\<^esub> u \<circ>\<^bsub>C\<^esub> dg (asrc a) \<cdot>\<^sub>a u =
      dg (Xphi C \<phi>) \<cdot>\<^sub>a (sphi_fun a \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub>
        (\<lambda>j\<in>Ob (ix (asrc a)). id\<^bsub>C\<^esub> (dg (asrc a) \<cdot>\<^sub>o j)) \<cdot> src\<^bsub>ix (asrc a)\<^esub> u"
    if u: "u \<in> Arr (ix (asrc a))" for u
    using C X u cJ \<phi>s sphi_arr_JArr[OF u] by (simp add: mem_M)
qed

text \<open>\<open>s\<^sub>a\<close> is a section of \<open>w\<^sub>\<phi>\<close>: \<open>q \<circ> s = id\<close>, and the components are \<open>id \<circ> id\<close>.\<close>

lemma sphi_wphi: "Dcomp C (wphi C \<phi>) (sphi C \<phi> a) = Did C (asrc a)"
proof (rule DArr_eqI)
  show "Dcomp C (wphi C \<phi>) (sphi C \<phi> a) \<in> DArr C"
    by (rule Dcomp_DArr[OF C sphi_DArr wphi_DArr[OF C ls \<phi>P]]) simp
  show "Did C (asrc a) \<in> DArr C"
    using C X by simp
  show "asrc (Dcomp C (wphi C \<phi>) (sphi C \<phi> a)) = asrc (Did C (asrc a))"
    using X by (simp add: DOb_M)
  show "atgt (Dcomp C (wphi C \<phi>) (sphi C \<phi> a)) = atgt (Did C (asrc a))"
    using X \<phi>s by (simp add: DOb_M)
  have "fcomp (ix (asrc a)) (qphi C \<phi>) (sphi_fun a) = idf (ix (asrc a))"
  proof (rule strict_functor_eqI[OF fcomp_strict[OF cJ sphi_fun_functor qphi_functor[OF C ls \<phi>P]]
        idf_strict[OF cJ]])
    show "agree (ix (asrc a)) (fcomp (ix (asrc a)) (qphi C \<phi>) (sphi_fun a)) (idf (ix (asrc a)))"
    proof (rule agreeI)
      show "fcomp (ix (asrc a)) (qphi C \<phi>) (sphi_fun a) \<cdot>\<^sub>o j = idf (ix (asrc a)) \<cdot>\<^sub>o j"
        if j: "j \<in> Ob (ix (asrc a))" for j
        using j sphi_obj_JOb[OF j] by (simp add: mem_M)
      show "fcomp (ix (asrc a)) (qphi C \<phi>) (sphi_fun a) \<cdot>\<^sub>a u = idf (ix (asrc a)) \<cdot>\<^sub>a u"
        if u: "u \<in> Arr (ix (asrc a))" for u
        using u sphi_arr_JArr[OF u] by (simp add: mem_M)
    qed
  qed
  then show "afun (Dcomp C (wphi C \<phi>) (sphi C \<phi> a)) = afun (Did C (asrc a))"
    by simp
  show "anat (Dcomp C (wphi C \<phi>) (sphi C \<phi> a)) = anat (Did C (asrc a))"
    using C X \<phi>s sphi_obj_JOb by (simp add: mem_M)
qed

text \<open>And \<open>t\<^sub>\<phi> \<circ> s\<^sub>a = a\<close>: \<open>\<pi> \<circ> s = p\<close>, and the components are \<open>\<alpha> j \<circ> id\<close>.\<close>

lemma sphi_tphi: "Dcomp C (tphi C \<phi>) (sphi C \<phi> a) = a"
proof (rule DArr_eqI)
  show "Dcomp C (tphi C \<phi>) (sphi C \<phi> a) \<in> DArr C"
    by (rule Dcomp_DArr[OF C sphi_DArr tphi_DArr[OF C ls \<phi>P]]) simp
  show "a \<in> DArr C"
    by (rule a)
  show "asrc (Dcomp C (tphi C \<phi>) (sphi C \<phi> a)) = asrc a"
    by simp
  show "atgt (Dcomp C (tphi C \<phi>) (sphi C \<phi> a)) = atgt a"
    using \<phi>t by simp
  have "fcomp (ix (asrc a)) (piphi C \<phi>) (sphi_fun a) = afun a"
  proof (rule strict_functor_eqI[OF fcomp_strict[OF cJ sphi_fun_functor piphi_functor[OF C ls \<phi>P]]
        DArr_strict[OF a]])
    show "agree (ix (asrc a)) (fcomp (ix (asrc a)) (piphi C \<phi>) (sphi_fun a)) (afun a)"
    proof (rule agreeI)
      show "fcomp (ix (asrc a)) (piphi C \<phi>) (sphi_fun a) \<cdot>\<^sub>o j = afun a \<cdot>\<^sub>o j"
        if j: "j \<in> Ob (ix (asrc a))" for j
        using j sphi_obj_JOb[OF j] by (simp add: mem_M)
      show "fcomp (ix (asrc a)) (piphi C \<phi>) (sphi_fun a) \<cdot>\<^sub>a u = afun a \<cdot>\<^sub>a u"
        if u: "u \<in> Arr (ix (asrc a))" for u
        using u sphi_arr_JArr[OF u] by (simp add: mem_M)
    qed
  qed
  then show "afun (Dcomp C (tphi C \<phi>) (sphi C \<phi> a)) = afun a"
    by simp
  have "anat (Dcomp C (tphi C \<phi>) (sphi C \<phi> a)) = (\<lambda>j\<in>Ob (ix (asrc a)). anat a \<cdot> j)"
    using C a sphi_obj_JOb by (simp add: mem_M)
  also have "\<dots> = anat a"
    by (rule DArr_anat_Lam[OF a, symmetric])
  finally show "anat (Dcomp C (tphi C \<phi>) (sphi C \<phi> a)) = anat a" .
qed

end

subsection \<open>The theorem\<close>

theorem colim_has_sections:
  assumes "category C" and "locally_small C"
  shows "has_sections (colim_functor C) (W0 C) (Diag C)"
  unfolding has_sections_def
proof (intro allI impI)
  note C = assms(1) and ls = assms(2)
  fix f g
  assume "M f" and "M g" and fA: "f \<in> Arr (Diag C)" and gA: "g \<in> Arr (Diag C)"
    and src_fg: "src\<^bsub>Diag C\<^esub> f = src\<^bsub>Diag C\<^esub> g" and tgt_fg: "tgt\<^bsub>Diag C\<^esub> f = tgt\<^bsub>Diag C\<^esub> g"
    and Afg: "colim_functor C \<cdot>\<^sub>a f = colim_functor C \<cdot>\<^sub>a g"
  have f: "f \<in> DArr C" and g: "g \<in> DArr C"
    using fA gA by simp_all
  have sfg: "asrc g = asrc f" and tfg: "atgt g = atgt f"
    using src_fg tgt_fg f g by simp_all
  let ?\<phi> = "colim_functor C \<cdot>\<^sub>a f"
  have \<phi>f: "colim_functor C \<cdot>\<^sub>a f = ?\<phi>" ..
  have \<phi>g: "colim_functor C \<cdot>\<^sub>a g = ?\<phi>"
    using Afg by simp
  have \<phi>P: "?\<phi> \<in> PArr C"
    using C ls f by simp
  let ?q = "wphi C ?\<phi>" and ?t = "tphi C ?\<phi>" and ?s = "sphi C ?\<phi> f" and ?s' = "sphi C ?\<phi> g"
  have q: "?q \<in> W0 C"
    by (rule wphi_W0[OF C ls \<phi>P])
  have qD: "?q \<in> DArr C"
    by (rule wphi_DArr[OF C ls \<phi>P])
  have t: "?t \<in> DArr C"
    by (rule tphi_DArr[OF C ls \<phi>P])
  have s: "?s \<in> DArr C"
    by (rule sphi_DArr[OF C ls f \<phi>f])
  have s': "?s' \<in> DArr C"
    by (rule sphi_DArr[OF C ls g \<phi>g])
  have qs: "Dcomp C ?q ?s = Did C (asrc f)"
    by (rule sphi_wphi[OF C ls f \<phi>f])
  have qs': "Dcomp C ?q ?s' = Did C (asrc f)"
    using sphi_wphi[OF C ls g \<phi>g] sfg by simp
  have ts: "Dcomp C ?t ?s = f"
    by (rule sphi_tphi[OF C ls f \<phi>f])
  have ts': "Dcomp C ?t ?s' = g"
    by (rule sphi_tphi[OF C ls g \<phi>g])
  have "?q \<in> W0 C \<and> ?t \<in> Arr (Diag C) \<and> ?s \<in> Arr (Diag C) \<and> ?s' \<in> Arr (Diag C) \<and>
      tgt\<^bsub>Diag C\<^esub> ?q = src\<^bsub>Diag C\<^esub> f \<and> src\<^bsub>Diag C\<^esub> ?t = src\<^bsub>Diag C\<^esub> ?q \<and>
      tgt\<^bsub>Diag C\<^esub> ?t = tgt\<^bsub>Diag C\<^esub> f \<and>
      src\<^bsub>Diag C\<^esub> ?s = src\<^bsub>Diag C\<^esub> f \<and> tgt\<^bsub>Diag C\<^esub> ?s = src\<^bsub>Diag C\<^esub> ?q \<and>
      src\<^bsub>Diag C\<^esub> ?s' = src\<^bsub>Diag C\<^esub> f \<and> tgt\<^bsub>Diag C\<^esub> ?s' = src\<^bsub>Diag C\<^esub> ?q \<and>
      ?q \<circ>\<^bsub>Diag C\<^esub> ?s = id\<^bsub>Diag C\<^esub> (src\<^bsub>Diag C\<^esub> f) \<and> ?q \<circ>\<^bsub>Diag C\<^esub> ?s' = id\<^bsub>Diag C\<^esub> (src\<^bsub>Diag C\<^esub> f) \<and>
      ?t \<circ>\<^bsub>Diag C\<^esub> ?s = f \<and> ?t \<circ>\<^bsub>Diag C\<^esub> ?s' = g"
    using q qD t s s' qs qs' ts ts' f g sfg by simp
  then show "\<exists>\<^sub>s q t s s'. q \<in> W0 C \<and> t \<in> Arr (Diag C) \<and> s \<in> Arr (Diag C) \<and> s' \<in> Arr (Diag C) \<and>
      tgt\<^bsub>Diag C\<^esub> q = src\<^bsub>Diag C\<^esub> f \<and> src\<^bsub>Diag C\<^esub> t = src\<^bsub>Diag C\<^esub> q \<and>
      tgt\<^bsub>Diag C\<^esub> t = tgt\<^bsub>Diag C\<^esub> f \<and>
      src\<^bsub>Diag C\<^esub> s = src\<^bsub>Diag C\<^esub> f \<and> tgt\<^bsub>Diag C\<^esub> s = src\<^bsub>Diag C\<^esub> q \<and>
      src\<^bsub>Diag C\<^esub> s' = src\<^bsub>Diag C\<^esub> f \<and> tgt\<^bsub>Diag C\<^esub> s' = src\<^bsub>Diag C\<^esub> q \<and>
      q \<circ>\<^bsub>Diag C\<^esub> s = id\<^bsub>Diag C\<^esub> (src\<^bsub>Diag C\<^esub> f) \<and> q \<circ>\<^bsub>Diag C\<^esub> s' = id\<^bsub>Diag C\<^esub> (src\<^bsub>Diag C\<^esub> f) \<and>
      t \<circ>\<^bsub>Diag C\<^esub> s = f \<and> t \<circ>\<^bsub>Diag C\<^esub> s' = g"
    using mem_M[OF q] mem_M[OF t] mem_M[OF s] mem_M[OF s'] by blast
qed

end
