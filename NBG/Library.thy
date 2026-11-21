section \<open>The library: classes, pairs, functions and tagged structures\<close>

theory Library
  imports Classes
begin

text \<open>
  The facts about the vocabulary of \<open>Classes\<close> that the category theory uses every day:
  membership in each operation, pairs and projections, when an operation yields a set,
  application of \<open>\<lambda>\<close>-functions, and the components of tagged structures. Every lemma carries
  the hypotheses that make it true for junk arguments too: an "ordered pair" with a proper
  class in it, a value of a class that is not a function, and so on.
\<close>

subsection \<open>Comprehension in the simplifier\<close>

text \<open>
  The simplifier proves the conditions \<open>dfn P\<close>, \<open>dcls T\<close> and \<open>dfun f\<close> of conditional rules
  with the method \<open>dfn\<close>, using the definability facts among its assumptions. It does not
  rewrite inside these conditions, so the method sees the formula as written, with its set
  quantifiers intact. This makes \<open>Coll_iff\<close> a simplification rule: a membership in a
  comprehension unfolds when the method shows the formula definable, and stays as it is when
  it does not.

  The rules below whose right-hand side introduces a quantifier quantify over sets (\<open>\<exists>\<^sub>s\<close>),
  so that rewriting inside a comprehension keeps it definable for the method.
\<close>

lemma dfn_weak_cong [cong]: "dfn P = dfn P"
  by (rule refl)

lemma dcls_weak_cong [cong]: "dcls T = dcls T"
  by (rule refl)

lemma dfun_weak_cong [cong]: "dfun f = dfun f"
  by (rule refl)

ML \<open>
structure Dfn_Solver =
struct

val heads = [\<^const_name>\<open>dfn\<close>, \<^const_name>\<open>dcls\<close>, \<^const_name>\<open>dfun\<close>];

fun has_head t =
  (case HOLogic.dest_Trueprop (Logic.strip_assums_concl t) of
    Const (c, _) $ _ => member (op =) heads c
  | _ => false)
  handle TERM _ => false;

fun tac ctxt = SUBGOAL (fn (t, i) =>
  if has_head t then
    let val facts = filter (has_head o Thm.prop_of) (Simplifier.prems_of ctxt)
    in Method.insert_tac ctxt facts i THEN Dfn.tac ctxt i end
  else no_tac);

val solver = mk_solver "dfn" tac;

end
\<close>

setup \<open>
  map_theory_simpset
    (Simplifier.add_unsafe_solver Dfn_Solver.solver #> Simplifier.add_safe_solver Dfn_Solver.solver)
\<close>

declare Coll_iff [simp]

text \<open>
  \<open>mem_M\<close> is not a simplification rule: it would rewrite away the hypotheses \<open>M x\<close> that
  \<open>auto\<close> and \<open>blast\<close> need for witnesses of set quantifiers. Added locally, \<open>simp add: mem_M\<close>
  turns \<open>M x\<close> into \<open>True\<close> whenever an assumption says \<open>x \<in> A\<close> for some \<open>A\<close>.
\<close>

subsection \<open>Subclasses and extensionality\<close>

text \<open>Inclusion and equality of classes, and which classes are sets.\<close>

lemma subclsI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  unfolding subcls_def by blast

lemma subclsD [elim, intro?]: "A \<subseteq> B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B"
  unfolding subcls_def by blast

lemma subclsCE [elim]: "A \<subseteq> B \<Longrightarrow> (x \<notin> A \<Longrightarrow> P) \<Longrightarrow> (x \<in> B \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding subcls_def by blast

lemma subcls_refl [simp]: "A \<subseteq> A"
  by blast

lemma subcls_trans [trans]: "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
  by blast

lemma subcls_antisym: "A \<subseteq> B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> A = B"
  by (rule ext) blast

lemma cls_eqI: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B"
  by (rule ext) blast

lemma cls_eq_iff: "A = B \<longleftrightarrow> (\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  using ext by blast

lemma M_subcls:
  assumes "M B" and "A \<subseteq> B"
  shows "M A"
proof -
  obtain z where "M z" and z: "\<And>u. u \<in> z \<longleftrightarrow> u \<in> B \<and> u \<in> A"
    using subsets[rule_format, OF \<open>M B\<close>, of A] by blast
  have "z = A"
    using z \<open>A \<subseteq> B\<close> by (intro ext) blast
  with \<open>M z\<close> show ?thesis
    by simp
qed

lemma M_iff_subcls: "M A \<longleftrightarrow> (\<exists>\<^sub>s y. A \<subseteq> y)"
  using M_subcls by blast

text \<open>Russell's class is not a set, so neither is the universe.\<close>

lemma Russell: "\<not> M \<lbrace>x. x \<notin> x\<rbrace>"
proof
  let ?R = "\<lbrace>x. x \<notin> x\<rbrace>"
  assume "M ?R"
  have "dfn (\<lambda>x. x \<notin> x)"
    by dfn
  from Coll_iff[OF this, of ?R] \<open>M ?R\<close> show False
    by blast
qed

subsection \<open>Membership in each operation\<close>

text \<open>
  What it means to be a member of each operation of \<open>Classes\<close>. The membership in a product, a
  \<open>\<lambda>\<close> and a tagged class is an existential and is not a simplification rule; its form for an
  ordered pair of sets is.
\<close>

lemma mem_Emp [simp]: "x \<notin> \<emptyset>"
  by (simp add: Emp_def)

lemma Emp_iff: "A = \<emptyset> \<longleftrightarrow> (\<forall>x. x \<notin> A)"
  by (auto intro: ext)

lemma mem_Univ [simp]: "x \<in> \<V> \<longleftrightarrow> M x"
  by (simp add: Univ_def)

lemma mem_inter [simp]: "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  by (auto simp: cinter_def intro: mem_M)

lemma mem_union [simp]: "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  by (auto simp: cunion_def intro: mem_M)

lemma mem_diff [simp]: "x \<in> A \<setminus> B \<longleftrightarrow> x \<in> A \<and> x \<notin> B"
  by (auto simp: cdiff_def intro: mem_M)

lemma mem_prod: "p \<in> A \<times> B \<longleftrightarrow> (\<exists>\<^sub>s x y. p = \<langle>x, y\<rangle> \<and> x \<in> A \<and> y \<in> B)"
  by (auto simp: cprod_def)

lemma opair_mem_prod [simp]: "M x \<Longrightarrow> M y \<Longrightarrow> \<langle>x, y\<rangle> \<in> A \<times> B \<longleftrightarrow> x \<in> A \<and> y \<in> B"
  by (auto simp: mem_prod)

lemma prodI [intro!]: "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> \<langle>x, y\<rangle> \<in> A \<times> B"
  by (metis mem_M opair_mem_prod)

lemma prodE [elim!]: "p \<in> A \<times> B \<Longrightarrow> (\<And>x y. p = \<langle>x, y\<rangle> \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp: mem_prod)

lemma mem_cdom [simp]: "x \<in> cdom R \<longleftrightarrow> M x \<and> (\<exists>\<^sub>s y. \<langle>x, y\<rangle> \<in> R)"
  by (simp add: cdom_def)

lemma mem_cran [simp]: "y \<in> cran R \<longleftrightarrow> M y \<and> (\<exists>\<^sub>s x. \<langle>x, y\<rangle> \<in> R)"
  by (simp add: cran_def)

lemma mem_Lam: "dcls t \<Longrightarrow> p \<in> (\<lambda>x\<in>A. t x) \<longleftrightarrow> (\<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>x, t x\<rangle>)"
  by (auto simp: Lam_def)

lemma mem_tag: "p \<in> tag i A \<longleftrightarrow> (\<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>i, x\<rangle>)"
  by (auto simp: tag_def)

lemma mem_cmp [simp]: "x \<in> cmp i C \<longleftrightarrow> M x \<and> \<langle>i, x\<rangle> \<in> C"
  by (simp add: cmp_def)

lemma Emp_subcls [simp]: "\<emptyset> \<subseteq> A"
  by auto

lemma subcls_Univ [simp]: "A \<subseteq> \<V>"
  by (auto intro: mem_M)

lemma Univ_not_M [simp]: "\<not> M \<V>"
  using Russell M_subcls[of \<V> "\<lbrace>x. x \<notin> x\<rbrace>"] subcls_Univ by blast

lemma union_Emp [simp]: "A \<union> \<emptyset> = A"
  by (rule ext) simp

lemma Emp_union [simp]: "\<emptyset> \<union> A = A"
  by (rule ext) simp

subsection \<open>Comprehension\<close>

text \<open>
  A comprehension depends only on what its formula says about sets, whether or not the
  formula is definable. With a definable formula it is the class it should be.
\<close>

lemma Coll_cong:
  assumes "\<And>x. M x \<Longrightarrow> P x \<longleftrightarrow> Q x"
  shows "\<lbrace>x. P x\<rbrace> = \<lbrace>x. Q x\<rbrace>"
proof -
  have "(\<lambda>C. \<forall>x. x \<in> C \<longleftrightarrow> M x \<and> P x) = (\<lambda>C. \<forall>x. x \<in> C \<longleftrightarrow> M x \<and> Q x)"
    using assms by (intro HOL.ext) blast
  then show ?thesis
    unfolding Coll_def by (rule arg_cong)
qed

lemma CollI: "dfn P \<Longrightarrow> M x \<Longrightarrow> P x \<Longrightarrow> x \<in> \<lbrace>x. P x\<rbrace>"
  by simp

lemma CollD: "x \<in> \<lbrace>x. P x\<rbrace> \<Longrightarrow> dfn P \<Longrightarrow> P x"
  by simp

lemma Coll_mem [simp]: "\<lbrace>x. x \<in> A\<rbrace> = A"
  by (rule ext) (auto intro: mem_M)

lemma Coll_eqI: "dfn P \<Longrightarrow> (\<And>x. M x \<Longrightarrow> P x \<longleftrightarrow> x \<in> A) \<Longrightarrow> \<lbrace>x. P x\<rbrace> = A"
  by (rule ext) (auto intro: mem_M)

subsection \<open>Singletons and ordered pairs\<close>

text \<open>
  Injectivity of pairs in the forms proofs need. A pair with a proper class in it is junk: if
  \<open>y\<close> is proper then \<open>\<langle>x, y\<rangle> = \<langle>x, x\<rangle>\<close>. Still, the first component of a pair is determined as
  soon as one side has a set there, and the second as soon as both second components are sets.
\<close>

lemma sng_neq_Emp [simp]: "M x \<Longrightarrow> sng x \<noteq> \<emptyset>"
  by (metis mem_Emp mem_sng)

lemma Emp_neq_sng [simp]: "M x \<Longrightarrow> \<emptyset> \<noteq> sng x"
  by (metis mem_Emp mem_sng)

lemma sng_eq_iff [simp]: "M x \<Longrightarrow> sng x = sng y \<longleftrightarrow> x = y"
  by (metis mem_sng)

lemma upair_proper_fst: "\<not> M x \<Longrightarrow> upair x y = sng y"
  by (rule ext) auto

lemma upair_proper_snd: "\<not> M y \<Longrightarrow> upair x y = sng x"
  by (rule ext) auto

lemma opair_proper_snd: "\<not> M y \<Longrightarrow> \<langle>x, y\<rangle> = \<langle>x, x\<rangle>"
  by (simp add: opair_def upair_proper_snd sng_def)

lemma opair_proper_fst: "\<not> M x \<Longrightarrow> \<langle>x, y\<rangle> = upair \<emptyset> (sng y)"
proof -
  assume "\<not> M x"
  then have "upair x x = \<emptyset>"
    by (intro ext) auto
  with \<open>\<not> M x\<close> show ?thesis
    by (simp add: opair_def upair_proper_fst)
qed

lemma opair_M_fst:
  assumes eq: "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle>" and "M x'"
  shows "M x"
proof (rule ccontr)
  assume "\<not> M x"
  then have "\<emptyset> \<in> \<langle>x, y\<rangle>"
    by (simp add: opair_proper_fst)
  with eq have "\<emptyset> \<in> \<langle>x', y'\<rangle>"
    by simp
  then have "\<emptyset> = upair x' x' \<or> \<emptyset> = upair x' y'"
    by (simp add: opair_def)
  moreover have "x' \<in> upair x' x'" and "x' \<in> upair x' y'"
    using \<open>M x'\<close> by simp_all
  ultimately show False
    by (metis mem_Emp)
qed

lemma opair_set_snd:
  assumes "M x"
  obtains y' where "M y'" and "\<langle>x, y\<rangle> = \<langle>x, y'\<rangle>"
proof (cases "M y")
  case True
  then show ?thesis
    using that by blast
next
  case False
  then show ?thesis
    using that[of x] \<open>M x\<close> by (simp add: opair_proper_snd)
qed

lemma opair_fst_eq:
  assumes eq: "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle>" and "M x'"
  shows "x = x'"
proof -
  have "M x"
    using eq \<open>M x'\<close> by (rule opair_M_fst)
  obtain v where "M v" and v: "\<langle>x, y\<rangle> = \<langle>x, v\<rangle>"
    using \<open>M x\<close> by (rule opair_set_snd)
  obtain v' where "M v'" and v': "\<langle>x', y'\<rangle> = \<langle>x', v'\<rangle>"
    using \<open>M x'\<close> by (rule opair_set_snd)
  have "\<langle>x, v\<rangle> = \<langle>x', v'\<rangle>"
    using eq v v' by metis
  then show ?thesis
    using \<open>M x\<close> \<open>M x'\<close> \<open>M v\<close> \<open>M v'\<close> by simp
qed

lemma opair_snd_eq:
  assumes eq: "\<langle>x, y\<rangle> = \<langle>x, y'\<rangle>" and "M y" and "M y'"
  shows "y = y'"
proof (cases "M x")
  case True
  then show ?thesis
    using assms by simp
next
  case False
  then have "upair \<emptyset> (sng y) = upair \<emptyset> (sng y')"
    using eq by (simp add: opair_proper_fst)
  then have "sng y \<in> upair \<emptyset> (sng y')"
    by (metis M_sng mem_upair)
  then have "sng y = sng y'"
    using \<open>M y\<close> by auto
  then show ?thesis
    using \<open>M y\<close> by simp
qed

lemma opair_inject:
  assumes "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle>" and "M x" and "M y" and "M x'" and "M y'"
  obtains "x = x'" and "y = y'"
  using assms by simp

subsection \<open>Projections and values are sets\<close>

text \<open>
  \<open>pfst\<close>, \<open>psnd\<close> and application always give sets, and they give \<open>\<emptyset>\<close> where they are undefined.
  The description \<open>\<iota>\<^sub>s\<close> behind them is a set in every case.
\<close>

lemma M_pfst [simp]: "M (pfst p)"
  by (simp add: pfst_def)

lemma M_psnd [simp]: "M (psnd p)"
  by (simp add: psnd_def)

lemma M_app [simp]: "M (F \<cdot> x)"
  by (simp add: app_def)

lemma the_set_default:
  assumes "\<not> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y))"
  shows "(\<iota>\<^sub>s y. P y) = \<emptyset>"
proof -
  have "(\<iota>\<^sub>s y. P y) = \<lbrace>z. False\<rbrace>"
    unfolding the_set_def by (rule Coll_cong) (use assms in blast)
  then show ?thesis
    by (simp only: Emp_def)
qed

lemma the_set_cong:
  assumes PQ: "\<And>y. M y \<Longrightarrow> P y \<longleftrightarrow> Q y"
  shows "(\<iota>\<^sub>s y. P y) = (\<iota>\<^sub>s y. Q y)"
proof (cases "\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y)")
  case True
  then obtain y where "M y" and "P y" and u: "\<And>y'. M y' \<Longrightarrow> P y' \<Longrightarrow> y' = y"
    by blast
  have "(\<iota>\<^sub>s y. P y) = y"
    using \<open>M y\<close> \<open>P y\<close> u by (rule the_set_eq)
  moreover have "(\<iota>\<^sub>s y. Q y) = y"
  proof (rule the_set_eq)
    show "M y"
      by fact
    show "Q y"
      using PQ[OF \<open>M y\<close>] \<open>P y\<close> by blast
    fix y'
    assume "M y'" and "Q y'"
    then show "y' = y"
      using PQ[OF \<open>M y'\<close>] u by blast
  qed
  ultimately show ?thesis
    by (rule trans[OF _ sym])
next
  case False
  have "\<not> (\<exists>\<^sub>s y. Q y \<and> (\<forall>\<^sub>s y'. Q y' \<longrightarrow> y' = y))"
  proof
    assume "\<exists>\<^sub>s y. Q y \<and> (\<forall>\<^sub>s y'. Q y' \<longrightarrow> y' = y)"
    then obtain y where "M y" and "Q y" and u: "\<And>y'. M y' \<Longrightarrow> Q y' \<Longrightarrow> y' = y"
      by blast
    have "P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y)"
      using PQ \<open>M y\<close> \<open>Q y\<close> u by blast
    with \<open>M y\<close> False show False
      by blast
  qed
  then have Q: "(\<iota>\<^sub>s y. Q y) = \<emptyset>"
    by (rule the_set_default)
  have "(\<iota>\<^sub>s y. P y) = \<emptyset>"
    using False by (rule the_set_default)
  from this Q show ?thesis
    by (rule trans[OF _ sym])
qed

lemma the_setI:
  assumes "M y" and "P y" and "\<And>y'. M y' \<Longrightarrow> P y' \<Longrightarrow> y' = y"
  shows "P (\<iota>\<^sub>s y. P y)"
proof -
  from assms have "(\<iota>\<^sub>s y. P y) = y"
    by (rule the_set_eq)
  with \<open>P y\<close> show ?thesis
    by (simp only:)
qed

lemma mem_the_set: "z \<in> (\<iota>\<^sub>s y. P y) \<longleftrightarrow> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)"
proof (cases "\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y)")
  case True
  then obtain y where "M y" and "P y" and u: "\<And>y'. M y' \<Longrightarrow> P y' \<Longrightarrow> y' = y"
    by blast
  then have eq: "(\<iota>\<^sub>s y. P y) = y"
    by (intro the_set_eq)
  show ?thesis
    unfolding eq using \<open>M y\<close> \<open>P y\<close> u by blast
next
  case False
  then have eq: "(\<iota>\<^sub>s y. P y) = \<emptyset>"
    by (rule the_set_default)
  show ?thesis
    unfolding eq using False mem_Emp by blast
qed

lemma pfst_nonpair: "\<not> (\<exists>\<^sub>s x y. p = \<langle>x, y\<rangle>) \<Longrightarrow> pfst p = \<emptyset>"
  unfolding pfst_def by (rule the_set_default) blast

lemma psnd_nonpair: "\<not> (\<exists>\<^sub>s x y. p = \<langle>x, y\<rangle>) \<Longrightarrow> psnd p = \<emptyset>"
  unfolding psnd_def by (rule the_set_default) blast

lemma app_eq: "M y \<Longrightarrow> \<langle>x, y\<rangle> \<in> F \<Longrightarrow> (\<And>y'. M y' \<Longrightarrow> \<langle>x, y'\<rangle> \<in> F \<Longrightarrow> y' = y) \<Longrightarrow> F \<cdot> x = y"
  unfolding app_def by (rule the_set_eq)

lemma app_undef: "\<not> (\<exists>\<^sub>s y. \<langle>x, y\<rangle> \<in> F) \<Longrightarrow> F \<cdot> x = \<emptyset>"
  unfolding app_def by (rule the_set_default) blast

lemma prod_pfst: "p \<in> A \<times> B \<Longrightarrow> pfst p \<in> A"
  by (auto simp: mem_M)

lemma prod_psnd: "p \<in> A \<times> B \<Longrightarrow> psnd p \<in> B"
  by (auto simp: mem_M)

lemma prod_eta: "p \<in> A \<times> B \<Longrightarrow> p = \<langle>pfst p, psnd p\<rangle>"
  by (auto simp: mem_M)

subsection \<open>Sets\<close>

text \<open>
  When an operation yields a set, and the axioms of NBG that make sets in the forms the
  development uses: separation, replacement, union and power set, each stated with a
  comprehension. A \<open>dfun\<close> term gives a set at every set (\<open>dfun_M\<close>), which is how the \<open>dfun_*\<close>
  rules of \<open>Classes\<close> turn into sethood facts.
\<close>

lemma dfun_M: "dfun f \<Longrightarrow> M x \<Longrightarrow> M (f x)"
  unfolding dfun_def by blast

lemma M_inter1 [simp]: "M A \<Longrightarrow> M (A \<inter> B)"
  by (erule M_subcls) auto

lemma M_inter2 [simp]: "M B \<Longrightarrow> M (A \<inter> B)"
  by (erule M_subcls) auto

lemma M_diff [simp]: "M A \<Longrightarrow> M (A \<setminus> B)"
  by (erule M_subcls) auto

lemma M_union: "M A \<Longrightarrow> M B \<Longrightarrow> M (A \<union> B)"
proof -
  assume "M A" "M B"
  then have "dfun (\<lambda>z. A \<union> B)"
    by dfn
  from this M_Emp show ?thesis
    by (rule dfun_M)
qed

lemma M_union_iff [simp]: "M (A \<union> B) \<longleftrightarrow> M A \<and> M B"
proof -
  have "A \<subseteq> A \<union> B" and "B \<subseteq> A \<union> B"
    by auto
  then show ?thesis
    using M_subcls[of "A \<union> B" A] M_subcls[of "A \<union> B" B] M_union by blast
qed

lemma M_prod [simp]: "M A \<Longrightarrow> M B \<Longrightarrow> M (A \<times> B)"
proof -
  assume "M A" "M B"
  then have "dfun (\<lambda>z. A \<times> B)"
    by dfn
  from this M_Emp show ?thesis
    by (rule dfun_M)
qed

lemma M_cdom [simp]: "M R \<Longrightarrow> M (cdom R)"
proof -
  assume "M R"
  then have "dfun (\<lambda>z. cdom R)"
    by dfn
  from this M_Emp show ?thesis
    by (rule dfun_M)
qed

lemma M_cran [simp]: "M R \<Longrightarrow> M (cran R)"
proof -
  assume "M R"
  then have "dfun (\<lambda>z. cran R)"
    by dfn
  from this M_Emp show ?thesis
    by (rule dfun_M)
qed

lemma M_tag: "M i \<Longrightarrow> M A \<Longrightarrow> M (tag i A)"
proof -
  assume "M i" "M A"
  then have "dfun (\<lambda>z. tag i A)"
    by dfn
  from this M_Emp show ?thesis
    by (rule dfun_M)
qed

lemma M_sep: "M A \<Longrightarrow> dfn P \<Longrightarrow> M \<lbrace>x. x \<in> A \<and> P x\<rbrace>"
  by (erule M_subcls) auto

lemma M_Coll_subcls: "M A \<Longrightarrow> dfn P \<Longrightarrow> (\<And>x. M x \<Longrightarrow> P x \<Longrightarrow> x \<in> A) \<Longrightarrow> M \<lbrace>x. P x\<rbrace>"
  by (erule M_subcls) auto

text \<open>The union of a set of sets.\<close>

lemma M_Union: "M A \<Longrightarrow> M \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y \<in> x\<rbrace>"
proof -
  assume "M A"
  then obtain U where "M U" and U_iff: "\<And>u. u \<in> U \<longleftrightarrow> (\<exists>v. u \<in> v \<and> v \<in> A)"
    using sum_set by blast
  have "\<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y \<in> x\<rbrace> = U"
    by (rule ext) (auto simp: U_iff intro: mem_M)
  with \<open>M U\<close> show ?thesis
    by simp
qed

text \<open>Replacement: the image of a set under a definable term.\<close>

lemma M_replace:
  assumes "M A" and "dcls t"
  shows "M \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y = t x\<rbrace>"
proof -
  let ?Y = "\<lbrace>p. \<exists>\<^sub>s u v. p = \<langle>u, v\<rangle> \<and> u \<in> A \<and> v = t u\<rbrace>"
  have Y_iff: "\<langle>u, v\<rangle> \<in> ?Y \<longleftrightarrow> u \<in> A \<and> v = t u" if "M u" and "M v" for u v
    using that \<open>dcls t\<close> by auto
  have "\<exists>S. M S \<and> (\<forall>v. M v \<longrightarrow> (v \<in> S \<longleftrightarrow> (\<exists>u. u \<in> A \<and> \<langle>u, v\<rangle> \<in> ?Y)))"
  proof (rule replacement[rule_format, OF \<open>M A\<close>])
    fix u v w
    assume "M u" "M v" "M w" "\<langle>u, v\<rangle> \<in> ?Y" "\<langle>u, w\<rangle> \<in> ?Y"
    then show "v = w"
      using Y_iff by blast
  qed
  then obtain S where "M S" and S_iff: "\<And>v. M v \<Longrightarrow> v \<in> S \<longleftrightarrow> (\<exists>u. u \<in> A \<and> \<langle>u, v\<rangle> \<in> ?Y)"
    by blast
  have "v \<in> \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y = t x\<rbrace> \<longleftrightarrow> v \<in> S" for v
  proof
    assume "v \<in> \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y = t x\<rbrace>"
    then obtain x where "M v" and "x \<in> A" and "v = t x"
      using \<open>dcls t\<close> by auto
    then have "\<langle>x, v\<rangle> \<in> ?Y"
      using Y_iff mem_M by blast
    with \<open>M v\<close> \<open>x \<in> A\<close> show "v \<in> S"
      using S_iff by blast
  next
    assume "v \<in> S"
    then have "M v"
      by (rule mem_M)
    then obtain u where "u \<in> A" and "\<langle>u, v\<rangle> \<in> ?Y"
      using S_iff \<open>v \<in> S\<close> by blast
    then have "v = t u"
      using Y_iff mem_M \<open>M v\<close> by blast
    with \<open>M v\<close> \<open>u \<in> A\<close> show "v \<in> \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y = t x\<rbrace>"
      using \<open>dcls t\<close> mem_M[of u A] by auto
  qed
  then have "\<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y = t x\<rbrace> = S"
    by (rule ext)
  with \<open>M S\<close> show ?thesis
    by simp
qed

text \<open>The union of a set-indexed family of sets.\<close>

lemma M_UN:
  assumes "M A" and "dcls T" and "\<And>x. x \<in> A \<Longrightarrow> M (T x)"
  shows "M \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y \<in> T x\<rbrace>"
proof -
  let ?R = "\<lbrace>z. \<exists>\<^sub>s x. x \<in> A \<and> z = T x\<rbrace>"
  have "M ?R"
    using \<open>M A\<close> \<open>dcls T\<close> by (rule M_replace)
  then have U: "M \<lbrace>y. \<exists>\<^sub>s z. z \<in> ?R \<and> y \<in> z\<rbrace>"
    by (rule M_Union)
  have "\<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y \<in> T x\<rbrace> \<subseteq> \<lbrace>y. \<exists>\<^sub>s z. z \<in> ?R \<and> y \<in> z\<rbrace>"
  proof
    fix y
    assume "y \<in> \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y \<in> T x\<rbrace>"
    then obtain x where "x \<in> A" and "y \<in> T x"
      using \<open>dcls T\<close> by auto
    moreover have "M (T x)"
      using \<open>x \<in> A\<close> by (rule assms(3))
    ultimately show "y \<in> \<lbrace>y. \<exists>\<^sub>s z. z \<in> ?R \<and> y \<in> z\<rbrace>"
      using \<open>dcls T\<close> mem_M[of x A] mem_M[of y "T x"] by auto
  qed
  with U show ?thesis
    by (rule M_subcls)
qed

text \<open>The class of subclasses of a set is a set.\<close>

lemma M_Pow: "M A \<Longrightarrow> M \<lbrace>x. x \<subseteq> A\<rbrace>"
proof -
  assume "M A"
  then obtain y where "M y" and y_iff: "\<And>u. M u \<Longrightarrow> u \<in> y \<longleftrightarrow> (\<forall>w. w \<in> u \<longrightarrow> w \<in> A)"
    using power_set by blast
  have "u \<in> y \<longleftrightarrow> M u \<and> u \<subseteq> A" for u
    using y_iff[of u] mem_M[of u y] by (auto simp: subcls_def)
  then have "\<lbrace>x. x \<subseteq> A\<rbrace> = y"
    by (intro ext) simp
  with \<open>M y\<close> show ?thesis
    by simp
qed

text \<open>A component of a set is a set, whatever the label: \<open>x \<in> cmp i C\<close> gives \<open>x \<in> upair i x \<in> \<langle>i, x\<rangle> \<in> C\<close>.\<close>

lemma M_cmp [simp]: "M C \<Longrightarrow> M (cmp i C)"
proof -
  assume "M C"
  let ?U = "\<lbrace>v. \<exists>\<^sub>s w. w \<in> C \<and> v \<in> w\<rbrace>"
  let ?UU = "\<lbrace>u. \<exists>\<^sub>s v. v \<in> ?U \<and> u \<in> v\<rbrace>"
  have "M ?U"
    using \<open>M C\<close> by (rule M_Union)
  then have "M ?UU"
    by (rule M_Union)
  moreover have "cmp i C \<subseteq> ?UU"
  proof
    fix x
    assume "x \<in> cmp i C"
    then have "M x" and "\<langle>i, x\<rangle> \<in> C"
      by simp_all
    have "upair i x \<in> \<langle>i, x\<rangle>"
      by (simp add: opair_def)
    moreover have "x \<in> upair i x"
      using \<open>M x\<close> by simp
    moreover have "upair i x \<in> ?U"
      using \<open>upair i x \<in> \<langle>i, x\<rangle>\<close> \<open>\<langle>i, x\<rangle> \<in> C\<close> by (auto intro: M_opair)
    ultimately have "\<exists>\<^sub>s v. v \<in> ?U \<and> x \<in> v"
      using M_upair by blast
    moreover have d: "dfn (\<lambda>u. \<exists>\<^sub>s v. v \<in> ?U \<and> u \<in> v)"
      by dfn
    ultimately show "x \<in> ?UU"
      using \<open>M x\<close> Coll_iff[OF d] by blast
  qed
  ultimately show ?thesis
    by (rule M_subcls)
qed

subsection \<open>Functions: \<open>\<lambda>\<close> and application\<close>

text \<open>
  A \<open>\<lambda>\<close> with a definable body is the class of pairs it should be. Applied to a member of its
  domain whose value is a set, it gives that value; outside its domain it gives \<open>\<emptyset>\<close>. Two
  canonical functions on the same domain that agree there are equal.
\<close>

lemma Lam_cong [cong]:
  "A = A' \<Longrightarrow> (\<And>x. x \<in> A' \<Longrightarrow> t x = t' x) \<Longrightarrow> (\<lambda>x\<in>A. t x) = (\<lambda>x\<in>A'. t' x)"
  unfolding Lam_def by (rule Coll_cong) auto

lemma Lam_eqI: "(\<And>x. x \<in> A \<Longrightarrow> t x = t' x) \<Longrightarrow> (\<lambda>x\<in>A. t x) = (\<lambda>x\<in>A. t' x)"
  by (rule Lam_cong) simp_all

lemma LamI: "dcls t \<Longrightarrow> x \<in> A \<Longrightarrow> \<langle>x, t x\<rangle> \<in> (\<lambda>u\<in>A. t u)"
  using mem_M[of x A] by (auto simp: mem_Lam)

lemma opair_mem_Lam [simp]:
  assumes "dcls t" and "M x" and "M y" and "M (t x)"
  shows "\<langle>x, y\<rangle> \<in> (\<lambda>u\<in>A. t u) \<longleftrightarrow> x \<in> A \<and> y = t x"
proof
  assume "\<langle>x, y\<rangle> \<in> (\<lambda>u\<in>A. t u)"
  then obtain x' where "M x'" and "x' \<in> A" and eq: "\<langle>x, y\<rangle> = \<langle>x', t x'\<rangle>"
    using \<open>dcls t\<close> by (auto simp: mem_Lam)
  from eq \<open>M x'\<close> have "x = x'"
    by (rule opair_fst_eq)
  with eq \<open>x' \<in> A\<close> have "x \<in> A" and "\<langle>x, y\<rangle> = \<langle>x, t x\<rangle>"
    by simp_all
  with assms show "x \<in> A \<and> y = t x"
    by simp
next
  assume "x \<in> A \<and> y = t x"
  with \<open>dcls t\<close> show "\<langle>x, y\<rangle> \<in> (\<lambda>u\<in>A. t u)"
    by (auto intro: LamI)
qed

lemma app_Lam [simp]: "dcls t \<Longrightarrow> x \<in> A \<Longrightarrow> M (t x) \<Longrightarrow> (\<lambda>u\<in>A. t u) \<cdot> x = t x"
  by (rule app_eq) (auto intro: LamI simp: mem_M)

lemma app_Lam_notin [simp]: "dcls t \<Longrightarrow> x \<notin> A \<Longrightarrow> (\<lambda>u\<in>A. t u) \<cdot> x = \<emptyset>"
  by (rule app_undef) (auto simp: mem_Lam dest: opair_fst_eq)

lemma cdom_Lam [simp]: "dcls t \<Longrightarrow> cdom (\<lambda>u\<in>A. t u) = A"
proof (rule ext)
  fix x
  assume "dcls t"
  show "x \<in> cdom (\<lambda>u\<in>A. t u) \<longleftrightarrow> x \<in> A"
  proof
    assume "x \<in> cdom (\<lambda>u\<in>A. t u)"
    then obtain y x' where "M x'" and "x' \<in> A" and "\<langle>x, y\<rangle> = \<langle>x', t x'\<rangle>"
      using \<open>dcls t\<close> by (auto simp: mem_Lam)
    then show "x \<in> A"
      using opair_fst_eq by blast
  next
    assume "x \<in> A"
    then have "M x"
      by (rule mem_M)
    then obtain v where "M v" and v: "\<langle>x, t x\<rangle> = \<langle>x, v\<rangle>"
      by (rule opair_set_snd)
    have "\<langle>x, t x\<rangle> \<in> (\<lambda>u\<in>A. t u)"
      using \<open>dcls t\<close> \<open>x \<in> A\<close> by (rule LamI)
    with v \<open>M v\<close> \<open>M x\<close> show "x \<in> cdom (\<lambda>u\<in>A. t u)"
      by auto
  qed
qed

lemma mem_cran_Lam:
  assumes "dcls t" and "\<And>x. x \<in> A \<Longrightarrow> M (t x)"
  shows "y \<in> cran (\<lambda>u\<in>A. t u) \<longleftrightarrow> (\<exists>\<^sub>s x. x \<in> A \<and> y = t x)"
  using assms by (auto simp: mem_Lam intro: mem_M)

lemma M_Lam: "M A \<Longrightarrow> dcls t \<Longrightarrow> M (\<lambda>u\<in>A. t u)"
proof -
  assume "M A" "dcls t"
  then have "dfun (\<lambda>z. \<lambda>u\<in>A. t u)"
    by dfn
  from this M_Emp show ?thesis
    by (rule dfun_M)
qed

lemma M_Lam_iff [simp]: "dcls t \<Longrightarrow> M (\<lambda>u\<in>A. t u) \<longleftrightarrow> M A"
  using M_Lam M_cdom cdom_Lam by metis

lemma fun_ext:
  assumes "F = (\<lambda>x\<in>A. F \<cdot> x)" and "G = (\<lambda>x\<in>A. G \<cdot> x)" and "\<And>x. x \<in> A \<Longrightarrow> F \<cdot> x = G \<cdot> x"
  shows "F = G"
proof -
  have "F = (\<lambda>x\<in>A. F \<cdot> x)"
    by (fact assms(1))
  also have "\<dots> = (\<lambda>x\<in>A. G \<cdot> x)"
    using assms(3) by (rule Lam_eqI)
  also have "\<dots> = G"
    using assms(2) by (rule sym)
  finally show ?thesis .
qed

lemma Lam_eq_iff:
  assumes "dcls t" and "dcls t'" and "\<And>x. x \<in> A \<Longrightarrow> M (t x)" and "\<And>x. x \<in> A \<Longrightarrow> M (t' x)"
  shows "(\<lambda>x\<in>A. t x) = (\<lambda>x\<in>A. t' x) \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> t x = t' x)"
proof
  assume eq: "(\<lambda>x\<in>A. t x) = (\<lambda>x\<in>A. t' x)"
  show "\<forall>x. x \<in> A \<longrightarrow> t x = t' x"
  proof (intro allI impI)
    fix x
    assume "x \<in> A"
    have "t x = (\<lambda>x\<in>A. t x) \<cdot> x"
      using assms \<open>x \<in> A\<close> by simp
    also have "\<dots> = (\<lambda>x\<in>A. t' x) \<cdot> x"
      by (simp only: eq)
    also have "\<dots> = t' x"
      using assms \<open>x \<in> A\<close> by simp
    finally show "t x = t' x" .
  qed
next
  assume "\<forall>x. x \<in> A \<longrightarrow> t x = t' x"
  then show "(\<lambda>x\<in>A. t x) = (\<lambda>x\<in>A. t' x)"
    by (intro Lam_eqI) blast
qed

subsection \<open>Tagged structures\<close>

text \<open>
  A structure is a union of tagged components, \<open>tag l0 A \<union> \<dots> \<union> tag l5 F\<close>. The labels are
  distinct sets, \<open>cmp\<close> distributes over \<open>\<union>\<close> and picks out the component with its label, so the
  simplifier reads every component back off such a union. The structure is a set exactly when
  every component is.
\<close>

lemma labels_distinct [simp]:
  "l0 \<noteq> l1" "l0 \<noteq> l2" "l0 \<noteq> l3" "l0 \<noteq> l4" "l0 \<noteq> l5"
  "l1 \<noteq> l2" "l1 \<noteq> l3" "l1 \<noteq> l4" "l1 \<noteq> l5"
  "l2 \<noteq> l3" "l2 \<noteq> l4" "l2 \<noteq> l5"
  "l3 \<noteq> l4" "l3 \<noteq> l5"
  "l4 \<noteq> l5"
  by (simp_all add: l0_def l1_def l2_def l3_def l4_def l5_def)

lemmas labels_distinct' [simp] = labels_distinct[THEN not_sym]

lemma opair_mem_tag [simp]: "M x \<Longrightarrow> \<langle>i, x\<rangle> \<in> tag i A \<longleftrightarrow> x \<in> A"
  by (auto simp: mem_tag dest: opair_snd_eq)

lemma opair_mem_tag_other [simp]: "M j \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<langle>i, x\<rangle> \<notin> tag j A"
  by (auto simp: mem_tag dest: opair_fst_eq)

lemma cmp_tag [simp]: "cmp i (tag i A) = A"
  by (rule ext) (auto simp: mem_M)

lemma cmp_tag_other [simp]: "M j \<Longrightarrow> i \<noteq> j \<Longrightarrow> cmp i (tag j A) = \<emptyset>"
  by (rule ext) simp

lemma cmp_union [simp]: "cmp i (A \<union> B) = cmp i A \<union> cmp i B"
  by (rule ext) auto

lemma cmp_Emp [simp]: "cmp i \<emptyset> = \<emptyset>"
  by (rule ext) simp

lemma tag_Emp [simp]: "tag i \<emptyset> = \<emptyset>"
  by (rule ext) (simp add: mem_tag)

lemma M_tag_iff [simp]: "M i \<Longrightarrow> M (tag i A) \<longleftrightarrow> M A"
  using M_tag M_cmp[of "tag i A" i] by auto

end
