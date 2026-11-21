section \<open>Classes, sets, and which classes exist\<close>

theory Classes
  imports Class_Existence
begin

text \<open>
  The vocabulary of the whole development, and the rules that say which classes exist.

  Every operation below is a \<^emph>\<open>total, first-order definable\<close> operation on classes: it is given by
  a comprehension, never by a choice or description operator, and it has a definite value on
  every argument (usually the empty class where the textbook operation is undefined). So every
  statement written with these operations is a definite statement of NBG.
\<close>

subsection \<open>Quantifying over sets\<close>

abbreviation AllS :: "(cls \<Rightarrow> bool) \<Rightarrow> bool"  (binder \<open>\<forall>\<^sub>s\<close> 10)
  where "AllS P \<equiv> \<forall>x. M x \<longrightarrow> P x"

abbreviation ExS :: "(cls \<Rightarrow> bool) \<Rightarrow> bool"  (binder \<open>\<exists>\<^sub>s\<close> 10)
  where "ExS P \<equiv> \<exists>x. M x \<and> P x"

subsection \<open>Comprehension\<close>

text \<open>
  \<open>dfn P\<close>: the sets satisfying \<open>P\<close> form a class. This is a statement of NBG about \<open>P\<close>, to be
  proved from B1--B7 each time; it is not assumed for any \<open>P\<close>. \<open>\<lbrace>x. P x\<rbrace>\<close> is that class, and
  means nothing unless \<open>dfn P\<close> has been proved.
\<close>

definition dfn :: "(cls \<Rightarrow> bool) \<Rightarrow> bool"
  where "dfn P \<longleftrightarrow> (\<exists>C. \<forall>x. x \<in> C \<longleftrightarrow> M x \<and> P x)"

definition Coll :: "(cls \<Rightarrow> bool) \<Rightarrow> cls"
  where "Coll P = (THE C. \<forall>x. x \<in> C \<longleftrightarrow> M x \<and> P x)"

syntax "_Coll" :: "pttrn \<Rightarrow> bool \<Rightarrow> cls"  (\<open>(\<open>indent=1 notation=\<open>mixfix class comprehension\<close>\<close>\<lbrace>_ ./ _\<rbrace>)\<close>)
syntax_consts "_Coll" \<rightleftharpoons> Coll
translations "\<lbrace>x. P\<rbrace>" \<rightleftharpoons> "CONST Coll (\<lambda>x. P)"

subsection \<open>The operations\<close>

definition Emp :: cls  (\<open>\<emptyset>\<close>)
  where "\<emptyset> = \<lbrace>x. False\<rbrace>"

definition Univ :: cls  (\<open>\<V>\<close>)
  where "\<V> = \<lbrace>x. True\<rbrace>"

definition subcls :: "cls \<Rightarrow> cls \<Rightarrow> bool"  (infix \<open>\<subseteq>\<close> 50)
  where "A \<subseteq> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"

definition cinter :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (infixl \<open>\<inter>\<close> 70)
  where "A \<inter> B = \<lbrace>x. x \<in> A \<and> x \<in> B\<rbrace>"

definition cunion :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (infixl \<open>\<union>\<close> 65)
  where "A \<union> B = \<lbrace>x. x \<in> A \<or> x \<in> B\<rbrace>"

definition cdiff :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (infixl \<open>\<setminus>\<close> 65)
  where "A \<setminus> B = \<lbrace>x. x \<in> A \<and> x \<notin> B\<rbrace>"

definition sng :: "cls \<Rightarrow> cls"
  where "sng x = upair x x"

text \<open>\<open>\<iota>\<^sub>s y. P y\<close>: the set satisfying \<open>P\<close> if there is exactly one, and the empty set otherwise.\<close>

definition the_set :: "(cls \<Rightarrow> bool) \<Rightarrow> cls"  (binder \<open>\<iota>\<^sub>s\<close> 10)
  where "the_set P = \<lbrace>z. \<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y\<rbrace>"

text \<open>The components of an ordered pair; the empty set on anything that is not a pair of sets.\<close>

definition pfst :: "cls \<Rightarrow> cls"
  where "pfst p = (\<iota>\<^sub>s x. \<exists>\<^sub>s y. p = \<langle>x, y\<rangle>)"

definition psnd :: "cls \<Rightarrow> cls"
  where "psnd p = (\<iota>\<^sub>s y. \<exists>\<^sub>s x. p = \<langle>x, y\<rangle>)"

definition cprod :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (infixr \<open>\<times>\<close> 80)
  where "A \<times> B = \<lbrace>p. \<exists>\<^sub>s x y. p = \<langle>x, y\<rangle> \<and> x \<in> A \<and> y \<in> B\<rbrace>"

definition cdom :: "cls \<Rightarrow> cls"
  where "cdom R = \<lbrace>x. \<exists>\<^sub>s y. \<langle>x, y\<rangle> \<in> R\<rbrace>"

definition cran :: "cls \<Rightarrow> cls"
  where "cran R = \<lbrace>y. \<exists>\<^sub>s x. \<langle>x, y\<rangle> \<in> R\<rbrace>"

text \<open>
  \<open>F \<cdot> x\<close>: the value at \<open>x\<close> of a class \<open>F\<close> of ordered pairs; the empty set unless \<open>F\<close> has exactly
  one pair with first component \<open>x\<close>. It is always a set.
\<close>

definition app :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (infixl \<open>\<cdot>\<close> 90)
  where "F \<cdot> x = (\<iota>\<^sub>s y. \<langle>x, y\<rangle> \<in> F)"

text \<open>\<open>\<lambda>x\<in>A. t x\<close>: the class function on \<open>A\<close> with values \<open>t x\<close>, as a class of ordered pairs.\<close>

definition Lam :: "cls \<Rightarrow> (cls \<Rightarrow> cls) \<Rightarrow> cls"
  where "Lam A t = \<lbrace>p. \<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>x, t x\<rangle>\<rbrace>"

syntax "_Lam" :: "pttrn \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"  (\<open>(\<open>indent=3 notation=\<open>binder \<lambda>\<in>\<close>\<close>\<lambda>_\<in>_./ _)\<close> [0, 0, 3] 3)
syntax_consts "_Lam" \<rightleftharpoons> Lam
translations "\<lambda>x\<in>A. t" \<rightleftharpoons> "CONST Lam A (\<lambda>x. t)"

subsection \<open>Structures with several components\<close>

text \<open>
  A category has six components and may be a proper class, so it cannot be an ordered tuple.
  Instead a structure is one class, the union of its components each tagged with a label:
  \<open>tag i A\<close> is \<open>{i} \<times> A\<close>, and \<open>cmp i C\<close> recovers the component with label \<open>i\<close>. A structure is a
  set exactly when all its components are. The labels are the first six Zermelo numerals.
\<close>

definition tag :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "tag i A = \<lbrace>p. \<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>i, x\<rangle>\<rbrace>"

definition cmp :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "cmp i C = \<lbrace>x. \<langle>i, x\<rangle> \<in> C\<rbrace>"

definition l0 :: cls where "l0 = \<emptyset>"
definition l1 :: cls where "l1 = sng l0"
definition l2 :: cls where "l2 = sng l1"
definition l3 :: cls where "l3 = sng l2"
definition l4 :: cls where "l4 = sng l3"
definition l5 :: cls where "l5 = sng l4"

subsection \<open>Definable terms\<close>

text \<open>
  \<open>dcls T\<close>: the class-valued term \<open>T\<close> is definable, that is, \<open>{\<langle>x, z\<rangle>. z \<in> T x}\<close> is a class.
  \<open>dfun f\<close>: moreover every \<open>f x\<close> is a set, so \<open>f\<close> is a class function on the universe.
  A constant class is a \<open>dcls\<close> term; it is a \<open>dfun\<close> term only if it is a set.
\<close>

definition dcls :: "(cls \<Rightarrow> cls) \<Rightarrow> bool"
  where "dcls T \<longleftrightarrow> dfn (\<lambda>p. psnd p \<in> T (pfst p))"

definition dfun :: "(cls \<Rightarrow> cls) \<Rightarrow> bool"
  where "dfun f \<longleftrightarrow> dcls f \<and> (\<forall>\<^sub>s x. M (f x))"

subsection \<open>The first facts\<close>

lemma ext: "(\<And>z. z \<in> X \<longleftrightarrow> z \<in> Y) \<Longrightarrow> X = Y"
  by (rule extensional)

lemma mem_M: "x \<in> A \<Longrightarrow> M x"
  by (rule member_set)

lemma Coll_iff: "dfn P \<Longrightarrow> x \<in> \<lbrace>x. P x\<rbrace> \<longleftrightarrow> M x \<and> P x"
proof -
  assume "dfn P"
  then obtain C where C: "\<forall>x. x \<in> C \<longleftrightarrow> M x \<and> P x" unfolding dfn_def by blast
  have "\<lbrace>x. P x\<rbrace> = C"
    unfolding Coll_def
  proof (rule the_equality)
    show "\<forall>x. x \<in> C \<longleftrightarrow> M x \<and> P x" by (fact C)
  next
    fix C' assume "\<forall>x. x \<in> C' \<longleftrightarrow> M x \<and> P x"
    then show "C' = C" using C by (blast intro: ext)
  qed
  then show ?thesis using C by simp
qed

text \<open>The empty class has no members; it is the empty set of the axiom.\<close>

lemma dfn_False: "dfn (\<lambda>x. False)"
  unfolding dfn_def using empty_exists by blast

lemma mem_Emp: "x \<notin> \<emptyset>"
  unfolding Emp_def using Coll_iff[OF dfn_False] by blast

text \<open>Pairs, singletons and the labels are sets whatever their arguments are.\<close>

lemma M_Emp [simp]: "M \<emptyset>"
proof -
  obtain e where e: "M e" "\<forall>u. u \<notin> e" using empty_exists by blast
  have "\<emptyset> = e" by (rule ext) (simp add: mem_Emp e(2))
  then show ?thesis using e(1) by simp
qed

lemma M_upair [simp]: "M (upair x y)"
  by (rule upair_set)

lemma M_sng [simp]: "M (sng x)"
  unfolding sng_def by (rule upair_set)

lemma M_opair [simp]: "M \<langle>x, y\<rangle>"
  by (rule opair_set)

lemma M_labels [simp]: "M l0" "M l1" "M l2" "M l3" "M l4" "M l5"
  by (simp_all add: l0_def l1_def l2_def l3_def l4_def l5_def)

text \<open>
  Pairs. An ordered pair with a proper class in it is still a set, but a meaningless one, so
  the facts about components are for pairs of sets.
\<close>

lemma mem_upair [simp]: "u \<in> upair x y \<longleftrightarrow> M u \<and> (u = x \<or> u = y)"
  by (rule upair_iff)

lemma mem_sng [simp]: "u \<in> sng x \<longleftrightarrow> M u \<and> u = x"
  by (simp add: sng_def)

lemma opair_eq [simp]:
  "M x \<Longrightarrow> M y \<Longrightarrow> M x' \<Longrightarrow> M y' \<Longrightarrow> \<langle>x, y\<rangle> = \<langle>x', y'\<rangle> \<longleftrightarrow> x = x' \<and> y = y'"
  using opair_inject by blast

text \<open>
  The comprehension in \<open>\<iota>\<^sub>s\<close> defines a class for every predicate, by cases on whether there is
  exactly one set satisfying it; so its members are known without a definability hypothesis.
\<close>

lemma the_set_dfn: "dfn (\<lambda>z. \<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)"
proof (cases "\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y)")
  case True
  then obtain y0 where y0: "M y0" "P y0" "\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y0" by blast
  have "z \<in> y0 \<longleftrightarrow> M z \<and> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)" for z
  proof
    assume "z \<in> y0"
    then show "M z \<and> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)"
      using y0 mem_M by blast
  next
    assume "M z \<and> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)"
    then obtain y where y: "M y" "P y" "z \<in> y" by blast
    then have "y = y0" using y0(3) by blast
    then show "z \<in> y0" using y(3) by simp
  qed
  then show ?thesis unfolding dfn_def by blast
next
  case False
  obtain e where e: "M e" "\<forall>u. u \<notin> e" using empty_exists by blast
  have "z \<notin> e" "\<not> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)" for z
    using False e(2) by blast+
  then have "\<forall>z. z \<in> e \<longleftrightarrow> M z \<and> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)" by blast
  then show ?thesis unfolding dfn_def by blast
qed

lemma mem_the_set: "z \<in> (\<iota>\<^sub>s y. P y) \<longleftrightarrow> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)"
proof -
  have "z \<in> (\<iota>\<^sub>s y. P y) \<longleftrightarrow> M z \<and> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y) \<and> z \<in> y)"
    unfolding the_set_def by (rule Coll_iff[OF the_set_dfn])
  then show ?thesis using mem_M by blast
qed

lemma the_set_eq: "M y \<Longrightarrow> P y \<Longrightarrow> (\<And>y'. M y' \<Longrightarrow> P y' \<Longrightarrow> y' = y) \<Longrightarrow> (\<iota>\<^sub>s y. P y) = y"
proof -
  assume y: "M y" "P y" and u: "\<And>y'. M y' \<Longrightarrow> P y' \<Longrightarrow> y' = y"
  show ?thesis
  proof (rule ext)
    fix z
    show "z \<in> (\<iota>\<^sub>s y. P y) \<longleftrightarrow> z \<in> y"
    proof
      assume "z \<in> (\<iota>\<^sub>s y. P y)"
      then obtain y' where y': "M y'" "P y'" "z \<in> y'" unfolding mem_the_set by blast
      then show "z \<in> y" using u[OF y'(1,2)] by simp
    next
      assume "z \<in> y"
      then show "z \<in> (\<iota>\<^sub>s y. P y)" unfolding mem_the_set using y u by blast
    qed
  qed
qed

lemma the_set_none: "\<not> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y)) \<Longrightarrow> (\<iota>\<^sub>s y. P y) = \<emptyset>"
proof -
  assume none: "\<not> (\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y))"
  show ?thesis
  proof (rule ext)
    fix z
    have "z \<notin> (\<iota>\<^sub>s y. P y)" unfolding mem_the_set using none by blast
    then show "z \<in> (\<iota>\<^sub>s y. P y) \<longleftrightarrow> z \<in> \<emptyset>" using mem_Emp by blast
  qed
qed

lemma M_the_set [simp]: "M (\<iota>\<^sub>s y. P y)"
proof (cases "\<exists>\<^sub>s y. P y \<and> (\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y)")
  case True
  then obtain y0 where y0: "M y0" "P y0" "\<forall>\<^sub>s y'. P y' \<longrightarrow> y' = y0" by blast
  have "(\<iota>\<^sub>s y. P y) = y0" by (rule the_set_eq) (use y0 in blast)+
  then show ?thesis using y0(1) by simp
next
  case False
  then show ?thesis by (simp add: the_set_none)
qed

lemma pfst_opair [simp]: "M x \<Longrightarrow> M y \<Longrightarrow> pfst \<langle>x, y\<rangle> = x"
  unfolding pfst_def by (rule the_set_eq) auto

lemma psnd_opair [simp]: "M x \<Longrightarrow> M y \<Longrightarrow> psnd \<langle>x, y\<rangle> = y"
  unfolding psnd_def by (rule the_set_eq) auto

text \<open>On anything but a pair of sets the projections are empty, and they are always sets.\<close>

lemma pfst_nonpair: "\<not> (\<exists>\<^sub>s a b. p = \<langle>a, b\<rangle>) \<Longrightarrow> pfst p = \<emptyset>"
  unfolding pfst_def by (rule the_set_none) blast

lemma psnd_nonpair: "\<not> (\<exists>\<^sub>s a b. p = \<langle>a, b\<rangle>) \<Longrightarrow> psnd p = \<emptyset>"
  unfolding psnd_def by (rule the_set_none) blast

lemma M_pfst: "M (pfst p)"
  unfolding pfst_def by simp

lemma M_psnd: "M (psnd p)"
  unfolding psnd_def by simp

lemma mem_pfst: "z \<in> pfst p \<longleftrightarrow> (\<exists>\<^sub>s a b. p = \<langle>a, b\<rangle> \<and> z \<in> a)"
proof (cases "\<exists>\<^sub>s a b. p = \<langle>a, b\<rangle>")
  case True
  then obtain a b where "M a" "M b" "p = \<langle>a, b\<rangle>" by blast
  then show ?thesis by auto
next
  case False
  then show ?thesis by (auto simp: pfst_nonpair mem_Emp)
qed

lemma mem_psnd: "z \<in> psnd p \<longleftrightarrow> (\<exists>\<^sub>s a b. p = \<langle>a, b\<rangle> \<and> z \<in> b)"
proof (cases "\<exists>\<^sub>s a b. p = \<langle>a, b\<rangle>")
  case True
  then obtain a b where "M a" "M b" "p = \<langle>a, b\<rangle>" by blast
  then show ?thesis by auto
next
  case False
  then show ?thesis by (auto simp: psnd_nonpair mem_Emp)
qed

subsection \<open>Definability through the Class Existence Theorem\<close>

text \<open>
  A predicate is definable when some class agrees with it on sets, and a class-valued term is
  definable when some class of pairs agrees with it on pairs of sets. The Class Existence
  Theorem of \<open>Class_Existence\<close> gives such classes for the formulas of its datatype \<open>form\<close>.
\<close>

lemmas form_simps = feval_simps fbnd_simps

lemma dfn_iff_cls: "dfn P \<longleftrightarrow> (\<exists>C. \<forall>x. M x \<longrightarrow> (x \<in> C \<longleftrightarrow> P x))"
  unfolding dfn_def using mem_M by blast

lemma dfnE: "dfn P \<Longrightarrow> (\<And>C. (\<And>x. M x \<Longrightarrow> x \<in> C \<longleftrightarrow> P x) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding dfn_iff_cls by blast

lemma dfnI_form: "fbnd \<phi> 1 \<Longrightarrow> (\<And>x. M x \<Longrightarrow> feval \<phi> [x] \<longleftrightarrow> P x) \<Longrightarrow> dfn P"
proof -
  assume "fbnd \<phi> 1" and e: "\<And>x. M x \<Longrightarrow> feval \<phi> [x] \<longleftrightarrow> P x"
  then obtain C where "\<forall>x. M x \<longrightarrow> (x \<in> C \<longleftrightarrow> feval \<phi> [x])" using form_cls1 by blast
  then show ?thesis unfolding dfn_iff_cls using e by blast
qed

lemma dcls_iff_rel: "dcls T \<longleftrightarrow> (\<exists>R. \<forall>x z. M x \<longrightarrow> M z \<longrightarrow> (\<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x))"
proof
  assume "dcls T"
  then obtain C where C: "\<And>p. M p \<Longrightarrow> p \<in> C \<longleftrightarrow> psnd p \<in> T (pfst p)"
    unfolding dcls_def by (rule dfnE) blast
  have "\<forall>x z. M x \<longrightarrow> M z \<longrightarrow> (\<langle>x, z\<rangle> \<in> C \<longleftrightarrow> z \<in> T x)" using C by simp
  then show "\<exists>R. \<forall>x z. M x \<longrightarrow> M z \<longrightarrow> (\<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x)" by blast
next
  assume "\<exists>R. \<forall>x z. M x \<longrightarrow> M z \<longrightarrow> (\<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x)"
  then obtain R where R: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x" by blast
  show "dcls T"
    unfolding dcls_def
  proof (rule dfnI_form[where \<phi> = "FOr (FEx (FEx (FAnd (FOp 2 1 0) (FIn2 1 0 R))))
      (FAnd (FNot (FEx (FEx (FOp 2 1 0)))) (FCst (\<emptyset> \<in> T \<emptyset>)))"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 p)
    show ?case
    proof (cases "\<exists>\<^sub>s a b. p = \<langle>a, b\<rangle>")
      case True
      then obtain a b where "M a" "M b" "p = \<langle>a, b\<rangle>" by blast
      then show ?thesis using R by (auto simp: form_simps)
    next
      case False
      then show ?thesis by (auto simp: form_simps pfst_nonpair psnd_nonpair)
    qed
  qed
qed

lemma dclsE: "dcls T \<Longrightarrow> (\<And>R. (\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding dcls_iff_rel by blast

lemma dclsI_form: "fbnd \<phi> 2 \<Longrightarrow> (\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> feval \<phi> [z, x] \<longleftrightarrow> z \<in> T x) \<Longrightarrow> dcls T"
proof -
  assume "fbnd \<phi> 2" and e: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> feval \<phi> [z, x] \<longleftrightarrow> z \<in> T x"
  then obtain C where "\<forall>x z. M x \<longrightarrow> M z \<longrightarrow> (\<langle>x, z\<rangle> \<in> C \<longleftrightarrow> feval \<phi> [z, x])"
    using form_cls2 by blast
  then show ?thesis unfolding dcls_iff_rel using e by blast
qed

lemma dfunE:
  "dfun f \<Longrightarrow> (\<And>F. (\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> F \<longleftrightarrow> z \<in> f x) \<Longrightarrow> (\<And>x. M x \<Longrightarrow> M (f x)) \<Longrightarrow> thesis)
    \<Longrightarrow> thesis"
  unfolding dfun_def dcls_iff_rel by blast

text \<open>A set is the section of a class of pairs exactly when it has the same members.\<close>

lemma sec_eq: "(\<And>z. M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x) \<Longrightarrow> (\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> R)) \<longleftrightarrow> y = T x"
  by (simp add: eq_iff_members)

subsection \<open>The rules of class existence\<close>

text \<open>
  These rules are the Class Existence Theorem of NBG, in a form a proof search can use: each
  one is a theorem proved from B1--B7, and together they say that a formula defines a class
  when its quantifiers range over sets. The method \<open>dfn\<close> applies them backwards. There is no
  rule for a quantifier over classes, so the method fails on an impredicative formula, as it
  must.

  A definition that introduces a predicate or an operation adds its own rule to \<open>dfn_rules\<close>,
  stated for arbitrary definable arguments, so that later formulas can mention it.

  The core rules come first, each proved by exhibiting a formula of \<open>Class_Existence\<close>; the
  others follow from them, most by the method \<open>dfn\<close> itself.
\<close>

named_theorems dfn_rules \<open>rules of class existence, used by the method dfn\<close>

lemma dfn_const [dfn_rules]: "dfn (\<lambda>x. Q)"
  by (rule dfnI_form[where \<phi> = "FCst Q"]) (simp_all add: form_simps)

lemma dfn_not [dfn_rules]: "dfn P \<Longrightarrow> dfn (\<lambda>x. \<not> P x)"
proof -
  assume "dfn P"
  then obtain C where C: "\<And>x. M x \<Longrightarrow> x \<in> C \<longleftrightarrow> P x" by (rule dfnE) blast
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FNot (FIn 0 C)"]) (simp_all add: form_simps C)
qed

lemma dfn_conj [dfn_rules]: "dfn P \<Longrightarrow> dfn Q \<Longrightarrow> dfn (\<lambda>x. P x \<and> Q x)"
proof -
  assume "dfn P" "dfn Q"
  then obtain C D where C: "\<And>x. M x \<Longrightarrow> x \<in> C \<longleftrightarrow> P x" and D: "\<And>x. M x \<Longrightarrow> x \<in> D \<longleftrightarrow> Q x"
    by (metis dfnE)
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FAnd (FIn 0 C) (FIn 0 D)"]) (simp_all add: form_simps C D)
qed

lemma dfn_disj [dfn_rules]: "dfn P \<Longrightarrow> dfn Q \<Longrightarrow> dfn (\<lambda>x. P x \<or> Q x)"
proof -
  assume "dfn P" "dfn Q"
  then obtain C D where C: "\<And>x. M x \<Longrightarrow> x \<in> C \<longleftrightarrow> P x" and D: "\<And>x. M x \<Longrightarrow> x \<in> D \<longleftrightarrow> Q x"
    by (metis dfnE)
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FOr (FIn 0 C) (FIn 0 D)"]) (simp_all add: form_simps C D)
qed

lemma dfn_imp [dfn_rules]: "dfn P \<Longrightarrow> dfn Q \<Longrightarrow> dfn (\<lambda>x. P x \<longrightarrow> Q x)"
proof -
  assume "dfn P" "dfn Q"
  then obtain C D where C: "\<And>x. M x \<Longrightarrow> x \<in> C \<longleftrightarrow> P x" and D: "\<And>x. M x \<Longrightarrow> x \<in> D \<longleftrightarrow> Q x"
    by (metis dfnE)
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FOr (FNot (FIn 0 C)) (FIn 0 D)"]) (simp_all add: form_simps C D)
qed

lemma dfn_iff [dfn_rules]: "dfn P \<Longrightarrow> dfn Q \<Longrightarrow> dfn (\<lambda>x. P x \<longleftrightarrow> Q x)"
proof -
  assume "dfn P" "dfn Q"
  then obtain C D where C: "\<And>x. M x \<Longrightarrow> x \<in> C \<longleftrightarrow> P x" and D: "\<And>x. M x \<Longrightarrow> x \<in> D \<longleftrightarrow> Q x"
    by (metis dfnE)
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FIff (FIn 0 C) (FIn 0 D)"]) (simp_all add: form_simps C D)
qed

lemma dfn_ex [dfn_rules]: "dfn (\<lambda>p. P (pfst p) (psnd p)) \<Longrightarrow> dfn (\<lambda>x. \<exists>\<^sub>s y. P x y)"
proof -
  assume "dfn (\<lambda>p. P (pfst p) (psnd p))"
  then obtain C where C: "\<And>p. M p \<Longrightarrow> p \<in> C \<longleftrightarrow> P (pfst p) (psnd p)" by (rule dfnE) blast
  have C2: "\<langle>x, y\<rangle> \<in> C \<longleftrightarrow> P x y" if "M x" "M y" for x y using C[of "\<langle>x, y\<rangle>"] that by simp
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FEx (FIn2 1 0 C)"]) (auto simp: form_simps C2)
qed

lemma dfn_all [dfn_rules]: "dfn (\<lambda>p. P (pfst p) (psnd p)) \<Longrightarrow> dfn (\<lambda>x. \<forall>\<^sub>s y. P x y)"
proof -
  assume "dfn (\<lambda>p. P (pfst p) (psnd p))"
  then obtain C where C: "\<And>p. M p \<Longrightarrow> p \<in> C \<longleftrightarrow> P (pfst p) (psnd p)" by (rule dfnE) blast
  have C2: "\<langle>x, y\<rangle> \<in> C \<longleftrightarrow> P x y" if "M x" "M y" for x y using C[of "\<langle>x, y\<rangle>"] that by simp
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FAll (FIn2 1 0 C)"]) (auto simp: form_simps C2)
qed

lemma dfn_mem [dfn_rules]: "dfun f \<Longrightarrow> dcls T \<Longrightarrow> dfn (\<lambda>x. f x \<in> T x)"
proof -
  assume "dfun f" "dcls T"
  from \<open>dfun f\<close> obtain F where F: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> F \<longleftrightarrow> z \<in> f x"
    and fM: "\<And>x. M x \<Longrightarrow> M (f x)" by (rule dfunE) blast
  from \<open>dcls T\<close> obtain R where R: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x" by (rule dclsE) blast
  show ?thesis
  proof (rule dfnI_form[where \<phi> = "FEx (FAnd (FEqC 0 1 F) (FIn2 1 0 R))"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x)
    have Fx: "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> F)) \<longleftrightarrow> y = f x" for y
      by (rule sec_eq[of x F f, OF F[OF 2]])
    show ?case using fM[OF 2] R[OF 2] by (auto simp: form_simps Fx)
  qed
qed

lemma dfn_eq [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dfn (\<lambda>x. S x = T x)"
proof -
  assume "dcls S" "dcls T"
  then obtain RS RT where RS: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> RS \<longleftrightarrow> z \<in> S x"
    and RT: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> RT \<longleftrightarrow> z \<in> T x" by (metis dclsE)
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FAll (FIff (FIn2 1 0 RS) (FIn2 1 0 RT))"])
      (simp_all add: form_simps RS RT eq_iff_members)
qed

lemma dfn_sub [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dfn (\<lambda>x. S x \<subseteq> T x)"
proof -
  assume "dcls S" "dcls T"
  then obtain RS RT where RS: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> RS \<longleftrightarrow> z \<in> S x"
    and RT: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> RT \<longleftrightarrow> z \<in> T x" by (metis dclsE)
  show ?thesis
    by (rule dfnI_form[where \<phi> = "FAll (FOr (FNot (FIn2 1 0 RS)) (FIn2 1 0 RT))"])
      (auto simp: form_simps RS RT subcls_def dest: mem_M)
qed

lemma dfn_M [dfn_rules]: "dcls T \<Longrightarrow> dfn (\<lambda>x. M (T x))"
proof -
  assume "dcls T"
  then obtain R where R: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x" by (rule dclsE) blast
  show ?thesis
  proof (rule dfnI_form[where \<phi> = "FEx (FEqC 0 1 R)"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x)
    have Rx: "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> R)) \<longleftrightarrow> y = T x" for y
      by (rule sec_eq[of x R T, OF R[OF 2(1)]])
    show ?case by (auto simp: form_simps Rx)
  qed
qed

lemma dcls_const [dfn_rules]: "dcls (\<lambda>x. A)"
  by (rule dclsI_form[where \<phi> = "FIn 0 A"]) (simp_all add: form_simps)

lemma dcls_dfun [dfn_rules]: "dfun f \<Longrightarrow> dcls f"
  unfolding dfun_def by blast

lemma dfun_id [dfn_rules]: "dfun (\<lambda>x. x)"
  proof -
  have "dcls (\<lambda>x. x)" by (rule dclsI_form[where \<phi> = "FMem 0 1"]) (simp_all add: form_simps)
  then show ?thesis unfolding dfun_def by simp
qed

lemma dfun_const [dfn_rules]: "M a \<Longrightarrow> dfun (\<lambda>x. a)"
  unfolding dfun_def using dcls_const by simp

lemma dfun_upair [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dfun (\<lambda>x. upair (S x) (T x))"
proof -
  assume "dcls S" "dcls T"
  then obtain RS RT where RS: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> RS \<longleftrightarrow> z \<in> S x"
    and RT: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> RT \<longleftrightarrow> z \<in> T x" by (metis dclsE)
  have "dcls (\<lambda>x. upair (S x) (T x))"
  proof (rule dclsI_form[where \<phi> = "FOr (FEqC 0 1 RS) (FEqC 0 1 RT)"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x z)
    have "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> RS)) \<longleftrightarrow> y = S x" for y
      by (rule sec_eq[of x RS S, OF RS[OF 2(1)]])
    moreover have "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> RT)) \<longleftrightarrow> y = T x" for y
      by (rule sec_eq[of x RT T, OF RT[OF 2(1)]])
    ultimately show ?case using 2 by (simp add: form_simps)
  qed
  then show ?thesis unfolding dfun_def by simp
qed

lemma dfun_sng [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. sng (T x))"
  unfolding sng_def by (rule dfun_upair)

lemma dfun_pair [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dfun (\<lambda>x. \<langle>S x, T x\<rangle>)"
proof -
  assume S: "dcls S" and T: "dcls T"
  have "dcls (\<lambda>x. upair (S x) (S x))" by (rule dcls_dfun, rule dfun_upair[OF S S])
  moreover have "dcls (\<lambda>x. upair (S x) (T x))" by (rule dcls_dfun, rule dfun_upair[OF S T])
  ultimately show ?thesis unfolding opair_def by (rule dfun_upair)
qed

lemma dfun_pfst [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. pfst (T x))"
proof -
  assume "dcls T"
  then obtain R where R: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x" by (rule dclsE) blast
  have "dcls (\<lambda>x. pfst (T x))"
  proof (rule dclsI_form[where
        \<phi> = "FEx (FEx (FEx (FAnd (FEqC 0 4 R) (FAnd (FOp 0 2 1) (FMem 3 2)))))"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x z)
    have Rx: "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> R)) \<longleftrightarrow> y = T x" for y
      by (rule sec_eq[of x R T, OF R[OF 2(1)]])
    show ?case by (auto simp: form_simps Rx mem_pfst) blast
  qed
  then show ?thesis unfolding dfun_def by (simp add: M_pfst)
qed

lemma dfun_psnd [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. psnd (T x))"
proof -
  assume "dcls T"
  then obtain R where R: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x" by (rule dclsE) blast
  have "dcls (\<lambda>x. psnd (T x))"
  proof (rule dclsI_form[where
        \<phi> = "FEx (FEx (FEx (FAnd (FEqC 0 4 R) (FAnd (FOp 0 2 1) (FMem 3 1)))))"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x z)
    have Rx: "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> R)) \<longleftrightarrow> y = T x" for y
      by (rule sec_eq[of x R T, OF R[OF 2(1)]])
    show ?case by (auto simp: form_simps Rx mem_psnd) blast
  qed
  then show ?thesis unfolding dfun_def by (simp add: M_psnd)
qed

lemma dfun_the [dfn_rules]: "dfn (\<lambda>p. P (pfst p) (psnd p)) \<Longrightarrow> dfun (\<lambda>x. \<iota>\<^sub>s y. P x y)"
proof -
  assume "dfn (\<lambda>p. P (pfst p) (psnd p))"
  then obtain C where C: "\<And>p. M p \<Longrightarrow> p \<in> C \<longleftrightarrow> P (pfst p) (psnd p)" by (rule dfnE) blast
  have C2: "\<langle>x, y\<rangle> \<in> C \<longleftrightarrow> P x y" if "M x" "M y" for x y using C[of "\<langle>x, y\<rangle>"] that by simp
  let ?\<phi> = "FEx (FAnd (FIn2 2 0 C) (FAnd (FAll (FOr (FNot (FIn2 3 0 C)) (FEq 0 1))) (FMem 1 0)))"
  have "dcls (\<lambda>x. \<iota>\<^sub>s y. P x y)"
  proof (rule dclsI_form[where \<phi> = ?\<phi>], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x z)
    have "feval ?\<phi> [z, x] \<longleftrightarrow>
        (\<exists>y. M y \<and> (\<langle>x, y\<rangle> \<in> C \<and> (\<forall>y'. M y' \<longrightarrow> \<langle>x, y'\<rangle> \<notin> C \<or> y' = y) \<and> z \<in> y))"
      by (simp add: form_simps)
    also have "\<dots> \<longleftrightarrow> (\<exists>y. M y \<and> (P x y \<and> (\<forall>y'. M y' \<longrightarrow> P x y' \<longrightarrow> y' = y) \<and> z \<in> y))"
    proof -
      have "(\<langle>x, y\<rangle> \<in> C \<and> (\<forall>y'. M y' \<longrightarrow> \<langle>x, y'\<rangle> \<notin> C \<or> y' = y) \<and> z \<in> y) \<longleftrightarrow>
          (P x y \<and> (\<forall>y'. M y' \<longrightarrow> P x y' \<longrightarrow> y' = y) \<and> z \<in> y)" if "M y" for y
        using C2 2(1) that by auto
      then show ?thesis by blast
    qed
    also have "\<dots> \<longleftrightarrow> z \<in> (\<iota>\<^sub>s y. P x y)" by (simp add: mem_the_set)
    finally show ?case .
  qed
  then show ?thesis unfolding dfun_def by simp
qed

text \<open>Substitution into a definable predicate or term. The method uses these for hypotheses.\<close>

lemma dfn_comp: "dfn P \<Longrightarrow> dfun g \<Longrightarrow> dfn (\<lambda>x. P (g x))"
proof -
  assume "dfn P" "dfun g"
  from \<open>dfn P\<close> obtain C where C: "\<And>x. M x \<Longrightarrow> x \<in> C \<longleftrightarrow> P x" by (rule dfnE) blast
  from \<open>dfun g\<close> obtain G where G: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> G \<longleftrightarrow> z \<in> g x"
    and gM: "\<And>x. M x \<Longrightarrow> M (g x)" by (rule dfunE) blast
  show ?thesis
  proof (rule dfnI_form[where \<phi> = "FEx (FAnd (FEqC 0 1 G) (FIn 0 C))"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x)
    have Gx: "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> G)) \<longleftrightarrow> y = g x" for y
      by (rule sec_eq[of x G g, OF G[OF 2]])
    show ?case using gM[OF 2] C[OF gM[OF 2]] by (auto simp: form_simps Gx)
  qed
qed

lemma dcls_comp: "dcls T \<Longrightarrow> dfun g \<Longrightarrow> dcls (\<lambda>x. T (g x))"
proof -
  assume "dcls T" "dfun g"
  from \<open>dcls T\<close> obtain R where R: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> R \<longleftrightarrow> z \<in> T x" by (rule dclsE) blast
  from \<open>dfun g\<close> obtain G where G: "\<And>x z. M x \<Longrightarrow> M z \<Longrightarrow> \<langle>x, z\<rangle> \<in> G \<longleftrightarrow> z \<in> g x"
    and gM: "\<And>x. M x \<Longrightarrow> M (g x)" by (rule dfunE) blast
  show ?thesis
  proof (rule dclsI_form[where \<phi> = "FEx (FAnd (FEqC 0 2 G) (FIn2 0 1 R))"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x z)
    have Gx: "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> \<langle>x, w\<rangle> \<in> G)) \<longleftrightarrow> y = g x" for y
      by (rule sec_eq[of x G g, OF G[OF 2(1)]])
    show ?case using gM[OF 2(1)] R[OF gM[OF 2(1)] 2(2)] by (auto simp: form_simps Gx)
  qed
qed

lemma dfun_comp: "dfun f \<Longrightarrow> dfun g \<Longrightarrow> dfun (\<lambda>x. f (g x))"
  proof -
  assume f: "dfun f" and g: "dfun g"
  have "dcls (\<lambda>x. f (g x))" by (rule dcls_comp[OF dcls_dfun[OF f] g])
  moreover have "M (f (g x))" if "M x" for x using f g that by (simp add: dfun_def)
  ultimately show ?thesis by (simp add: dfun_def)
qed

text \<open>
  Definability depends only on the values at sets; and a definable predicate or term of a pair
  can be composed with two definable terms.
\<close>

lemma dfn_cong: "dfn P \<Longrightarrow> (\<And>x. M x \<Longrightarrow> P x \<longleftrightarrow> Q x) \<Longrightarrow> dfn Q"
  unfolding dfn_iff_cls by blast

lemma dcls_cong: "dcls T \<Longrightarrow> (\<And>x. M x \<Longrightarrow> T x = T' x) \<Longrightarrow> dcls T'"
  unfolding dcls_def by (erule dfn_cong) (simp add: M_pfst)

lemma dfn2_comp:
  "dfn (\<lambda>p. P (pfst p) (psnd p)) \<Longrightarrow> dfun a \<Longrightarrow> dfun b \<Longrightarrow> dfn (\<lambda>x. P (a x) (b x))"
proof -
  assume P: "dfn (\<lambda>p. P (pfst p) (psnd p))" and a: "dfun a" and b: "dfun b"
  have "dfun (\<lambda>x. \<langle>a x, b x\<rangle>)" by (rule dfun_pair[OF dcls_dfun[OF a] dcls_dfun[OF b]])
  then have "dfn (\<lambda>x. P (pfst \<langle>a x, b x\<rangle>) (psnd \<langle>a x, b x\<rangle>))" by (rule dfn_comp[OF P])
  then show ?thesis by (rule dfn_cong) (use a b in \<open>simp add: dfun_def\<close>)
qed

lemma dcls2_comp:
  "dcls (\<lambda>p. t (pfst p) (psnd p)) \<Longrightarrow> dfun a \<Longrightarrow> dfun b \<Longrightarrow> dcls (\<lambda>x. t (a x) (b x))"
proof -
  assume t: "dcls (\<lambda>p. t (pfst p) (psnd p))" and a: "dfun a" and b: "dfun b"
  have "dfun (\<lambda>x. \<langle>a x, b x\<rangle>)" by (rule dfun_pair[OF dcls_dfun[OF a] dcls_dfun[OF b]])
  then have "dcls (\<lambda>x. t (pfst \<langle>a x, b x\<rangle>) (psnd \<langle>a x, b x\<rangle>))" by (rule dcls_comp[OF t])
  then show ?thesis by (rule dcls_cong) (use a b in \<open>simp add: dfun_def\<close>)
qed

lemma dfn_section: "dfn (\<lambda>p. P (pfst p) (psnd p)) \<Longrightarrow> M a \<Longrightarrow> dfn (P a)"
proof -
  assume H: "dfn (\<lambda>p. P (pfst p) (psnd p))" and a: "M a"
  show ?thesis using dfn2_comp[OF H dfun_const[OF a] dfun_id] by simp
qed

text \<open>
  The method: depth-first backward search with \<open>dfn_rules\<close>. A hypothesis \<open>dfn P\<close>, \<open>dcls T\<close> or
  \<open>dfun f\<close> of the goal is used both as it stands and composed with a definable term, which is
  what lets a rule about a new predicate be proved for arbitrary definable arguments.
\<close>

ML \<open>
structure Dfn =
struct

(* a side condition "M a" (a constant term must be a set): by the simplifier *)
fun side_tac ctxt = SUBGOAL (fn (t, i) =>
  (case HOLogic.dest_Trueprop (Logic.strip_assums_concl t) of
    Const (\<^const_name>\<open>M\<close>, _) $ _ => SOLVED' (asm_simp_tac ctxt) i
  | _ => no_tac)
  handle TERM _ => no_tac);

fun tac ctxt =
  Subgoal.FOCUS_PREMS (fn {context = ctxt', prems, ...} =>
    let
      val rules = Named_Theorems.get ctxt' @{named_theorems dfn_rules}
      val comps = @{thms dfn_comp dcls_comp dfun_comp}
      val derived = maps (fn prem => map_filter (fn c => try (fn () => prem RS c) ()) comps) prems
      fun search j =
        (resolve_tac ctxt' prems ORELSE'
          (resolve_tac ctxt' (derived @ rules) THEN_ALL_NEW search) ORELSE'
          side_tac ctxt') j
    in SOLVED' search 1 end) ctxt;

end
\<close>

method_setup dfn = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Dfn.tac ctxt))\<close>
  "prove that a predicate or a term is definable (dfn, dcls, dfun)"

text \<open>
  The remaining rules follow from the core ones. A comprehension \<open>\<lbrace>y. P x y\<rbrace>\<close> is definable in
  \<open>x\<close> when \<open>P\<close> is definable as a predicate of pairs; with it, each operation defined by a
  comprehension gets its rule by unfolding the definition and calling the method.
\<close>

lemma dcls_Coll [dfn_rules]: "dfn (\<lambda>p. P (pfst p) (psnd p)) \<Longrightarrow> dcls (\<lambda>x. \<lbrace>y. P x y\<rbrace>)"
proof -
  assume H: "dfn (\<lambda>p. P (pfst p) (psnd p))"
  then obtain C where C: "\<And>p. M p \<Longrightarrow> p \<in> C \<longleftrightarrow> P (pfst p) (psnd p)" by (rule dfnE) blast
  have C2: "\<langle>x, y\<rangle> \<in> C \<longleftrightarrow> P x y" if "M x" "M y" for x y using C[of "\<langle>x, y\<rangle>"] that by simp
  show ?thesis
  proof (rule dclsI_form[where \<phi> = "FIn2 1 0 C"], goal_cases)
    case 1
    show ?case by (simp add: form_simps)
  next
    case (2 x z)
    then show ?case using Coll_iff[OF dfn_section[OF H 2(1)], of z] by (simp add: form_simps C2)
  qed
qed

lemma dcls_inter [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dcls (\<lambda>x. S x \<inter> T x)"
  unfolding cinter_def by dfn

lemma dcls_union [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dcls (\<lambda>x. S x \<union> T x)"
  unfolding cunion_def by dfn

lemma dcls_diff [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dcls (\<lambda>x. S x \<setminus> T x)"
  unfolding cdiff_def by dfn

lemma dcls_prod [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dcls (\<lambda>x. S x \<times> T x)"
  unfolding cprod_def by dfn

lemma dcls_dom [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. cdom (T x))"
  unfolding cdom_def by dfn

lemma dcls_ran [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. cran (T x))"
  unfolding cran_def by dfn

lemma dcls_tag [dfn_rules]: "dfun i \<Longrightarrow> dcls T \<Longrightarrow> dcls (\<lambda>x. tag (i x) (T x))"
  unfolding tag_def by dfn

lemma dcls_cmp [dfn_rules]: "dfun i \<Longrightarrow> dcls T \<Longrightarrow> dcls (\<lambda>x. cmp (i x) (T x))"
  unfolding cmp_def by dfn

lemma dcls_Lam [dfn_rules]:
  "dcls T \<Longrightarrow> dcls (\<lambda>p. t (pfst p) (psnd p)) \<Longrightarrow> dcls (\<lambda>x. \<lambda>y\<in>T x. t x y)"
proof -
  assume T: "dcls T" and t: "dcls (\<lambda>p. t (pfst p) (psnd p))"
  have t2: "dcls (\<lambda>r. t (pfst (pfst r)) (psnd r))" by (rule dcls2_comp[OF t]; dfn)
  show ?thesis unfolding Lam_def using T t2 by dfn
qed

lemma dfun_app [dfn_rules]: "dcls T \<Longrightarrow> dcls S \<Longrightarrow> dfun (\<lambda>x. T x \<cdot> S x)"
  unfolding app_def by dfn

text \<open>The members of the operations, for the sethood halves of the \<open>dfun\<close> rules.\<close>

lemma mem_cinter: "z \<in> A \<inter> B \<longleftrightarrow> z \<in> A \<and> z \<in> B"
proof -
  have "dfn (\<lambda>z. z \<in> A \<and> z \<in> B)" by dfn
  then show ?thesis unfolding cinter_def by (auto simp: Coll_iff dest: mem_M)
qed

lemma mem_cunion: "z \<in> A \<union> B \<longleftrightarrow> z \<in> A \<or> z \<in> B"
proof -
  have "dfn (\<lambda>z. z \<in> A \<or> z \<in> B)" by dfn
  then show ?thesis unfolding cunion_def by (auto simp: Coll_iff dest: mem_M)
qed

lemma mem_cdiff: "z \<in> A \<setminus> B \<longleftrightarrow> z \<in> A \<and> z \<notin> B"
proof -
  have "dfn (\<lambda>z. z \<in> A \<and> z \<notin> B)" by dfn
  then show ?thesis unfolding cdiff_def by (auto simp: Coll_iff dest: mem_M)
qed

lemma mem_cprod: "p \<in> A \<times> B \<longleftrightarrow> (\<exists>\<^sub>s x y. p = \<langle>x, y\<rangle> \<and> x \<in> A \<and> y \<in> B)"
proof -
  have "dfn (\<lambda>p. \<exists>\<^sub>s x y. p = \<langle>x, y\<rangle> \<and> x \<in> A \<and> y \<in> B)" by dfn
  then show ?thesis unfolding cprod_def by (auto simp: Coll_iff)
qed

lemma mem_cdom: "x \<in> cdom R \<longleftrightarrow> M x \<and> (\<exists>\<^sub>s y. \<langle>x, y\<rangle> \<in> R)"
proof -
  have "dfn (\<lambda>x. \<exists>\<^sub>s y. \<langle>x, y\<rangle> \<in> R)" by dfn
  then show ?thesis unfolding cdom_def by (simp add: Coll_iff)
qed

lemma mem_cran: "y \<in> cran R \<longleftrightarrow> M y \<and> (\<exists>\<^sub>s x. \<langle>x, y\<rangle> \<in> R)"
proof -
  have "dfn (\<lambda>y. \<exists>\<^sub>s x. \<langle>x, y\<rangle> \<in> R)" by dfn
  then show ?thesis unfolding cran_def by (simp add: Coll_iff)
qed

lemma mem_tag: "p \<in> tag i A \<longleftrightarrow> (\<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>i, x\<rangle>)"
proof -
  have "dfn (\<lambda>p. \<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>i, x\<rangle>)" by dfn
  then show ?thesis unfolding tag_def by (auto simp: Coll_iff)
qed

lemma mem_cmp: "x \<in> cmp i C \<longleftrightarrow> M x \<and> \<langle>i, x\<rangle> \<in> C"
proof -
  have "dfn (\<lambda>x. \<langle>i, x\<rangle> \<in> C)" by dfn
  then show ?thesis unfolding cmp_def by (simp add: Coll_iff)
qed

lemma mem_Lam: "dcls t \<Longrightarrow> p \<in> (\<lambda>x\<in>A. t x) \<longleftrightarrow> (\<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>x, t x\<rangle>)"
proof -
  assume "dcls t"
  then have "dfn (\<lambda>p. \<exists>\<^sub>s x. x \<in> A \<and> p = \<langle>x, t x\<rangle>)" by dfn
  then show ?thesis unfolding Lam_def by (auto simp: Coll_iff)
qed

text \<open>A pair has its first component in a member, and its second component in a member.\<close>

lemma fst_in_opair: "M a \<Longrightarrow> a \<in> upair a a \<and> upair a a \<in> \<langle>a, b\<rangle>"
  by (simp add: opair_def)

lemma snd_in_opair: "M b \<Longrightarrow> b \<in> upair a b \<and> upair a b \<in> \<langle>a, b\<rangle>"
  by (simp add: opair_def)

lemma dfun_inter [dfn_rules]: "dfun f \<Longrightarrow> dcls T \<Longrightarrow> dfun (\<lambda>x. f x \<inter> T x)"
proof -
  assume f: "dfun f" and T: "dcls T"
  have "dcls (\<lambda>x. f x \<inter> T x)" by (rule dcls_inter[OF dcls_dfun[OF f] T])
  moreover have "M (f x \<inter> T x)" if "M x" for x
  proof (rule set_subset[of "f x"])
    show "M (f x)" using f that by (simp add: dfun_def)
  qed (simp add: mem_cinter)
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_union [dfn_rules]: "dfun f \<Longrightarrow> dfun g \<Longrightarrow> dfun (\<lambda>x. f x \<union> g x)"
proof -
  assume f: "dfun f" and g: "dfun g"
  have "dcls (\<lambda>x. f x \<union> g x)" by (rule dcls_union[OF dcls_dfun[OF f] dcls_dfun[OF g]])
  moreover have "M (f x \<union> g x)" if "M x" for x
  proof (rule set_union[of "f x" "g x"])
    show "M (f x)" using f that by (simp add: dfun_def)
    show "M (g x)" using g that by (simp add: dfun_def)
  qed (simp add: mem_cunion)
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_diff [dfn_rules]: "dfun f \<Longrightarrow> dcls T \<Longrightarrow> dfun (\<lambda>x. f x \<setminus> T x)"
proof -
  assume f: "dfun f" and T: "dcls T"
  have "dcls (\<lambda>x. f x \<setminus> T x)" by (rule dcls_diff[OF dcls_dfun[OF f] T])
  moreover have "M (f x \<setminus> T x)" if "M x" for x
  proof (rule set_subset[of "f x"])
    show "M (f x)" using f that by (simp add: dfun_def)
  qed (simp add: mem_cdiff)
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_prod [dfn_rules]: "dfun f \<Longrightarrow> dfun g \<Longrightarrow> dfun (\<lambda>x. f x \<times> g x)"
proof -
  assume f: "dfun f" and g: "dfun g"
  have "dcls (\<lambda>x. f x \<times> g x)" by (rule dcls_prod[OF dcls_dfun[OF f] dcls_dfun[OF g]])
  moreover have "M (f x \<times> g x)" if "M x" for x
  proof (rule set_pairs[of "f x" "g x"])
    show "M (f x)" using f that by (simp add: dfun_def)
    show "M (g x)" using g that by (simp add: dfun_def)
  qed (auto simp: mem_cprod)
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_dom [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. cdom (f x))"
proof -
  assume f: "dfun f"
  have "dcls (\<lambda>x. cdom (f x))" by (rule dcls_dom[OF dcls_dfun[OF f]])
  moreover have "M (cdom (f x))" if "M x" for x
  proof (rule set_Union2[of "f x"])
    show "M (f x)" using f that by (simp add: dfun_def)
  next
    fix z assume "z \<in> cdom (f x)"
    then obtain y where "M z" "M y" "\<langle>z, y\<rangle> \<in> f x" by (auto simp: mem_cdom)
    then show "\<exists>v w. z \<in> v \<and> v \<in> w \<and> w \<in> f x" using fst_in_opair[of z y] by blast
  qed
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_ran [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. cran (f x))"
proof -
  assume f: "dfun f"
  have "dcls (\<lambda>x. cran (f x))" by (rule dcls_ran[OF dcls_dfun[OF f]])
  moreover have "M (cran (f x))" if "M x" for x
  proof (rule set_Union2[of "f x"])
    show "M (f x)" using f that by (simp add: dfun_def)
  next
    fix z assume "z \<in> cran (f x)"
    then obtain a where "M z" "M a" "\<langle>a, z\<rangle> \<in> f x" by (auto simp: mem_cran)
    then show "\<exists>v w. z \<in> v \<and> v \<in> w \<and> w \<in> f x" using snd_in_opair[of z a] by blast
  qed
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_tag [dfn_rules]: "dfun i \<Longrightarrow> dfun f \<Longrightarrow> dfun (\<lambda>x. tag (i x) (f x))"
proof -
  assume i: "dfun i" and f: "dfun f"
  have "dcls (\<lambda>x. tag (i x) (f x))" by (rule dcls_tag[OF i dcls_dfun[OF f]])
  moreover have "M (tag (i x) (f x))" if "M x" for x
  proof (rule set_pairs[of "sng (i x)" "f x"])
    show "M (sng (i x))" by simp
    show "M (f x)" using f that by (simp add: dfun_def)
  qed (use i that in \<open>auto simp: mem_tag dfun_def\<close>)
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_cmp [dfn_rules]: "dfun i \<Longrightarrow> dfun f \<Longrightarrow> dfun (\<lambda>x. cmp (i x) (f x))"
proof -
  assume i: "dfun i" and f: "dfun f"
  have "dcls (\<lambda>x. cmp (i x) (f x))" by (rule dcls_cmp[OF i dcls_dfun[OF f]])
  moreover have "M (cmp (i x) (f x))" if "M x" for x
  proof (rule set_Union2[of "f x"])
    show "M (f x)" using f that by (simp add: dfun_def)
  next
    fix z assume "z \<in> cmp (i x) (f x)"
    then have "M z" "\<langle>i x, z\<rangle> \<in> f x" by (auto simp: mem_cmp)
    then show "\<exists>v w. z \<in> v \<and> v \<in> w \<and> w \<in> f x" using snd_in_opair[of z "i x"] by blast
  qed
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_Lam [dfn_rules]:
  "dfun f \<Longrightarrow> dcls (\<lambda>p. t (pfst p) (psnd p)) \<Longrightarrow> dfun (\<lambda>x. \<lambda>y\<in>f x. t x y)"
proof -
  assume f: "dfun f" and t: "dcls (\<lambda>p. t (pfst p) (psnd p))"
  have "dcls (\<lambda>x. \<lambda>y\<in>f x. t x y)" by (rule dcls_Lam[OF dcls_dfun[OF f] t])
  moreover have "M (\<lambda>y\<in>f x. t x y)" if x: "M x" for x
  proof -
    have tx: "dcls (t x)" using dcls2_comp[OF t dfun_const[OF x] dfun_id] by simp
    have "dfn (\<lambda>q. psnd q = \<langle>pfst q, t x (pfst q)\<rangle>)" using tx by dfn
    then obtain Y where Y0: "\<And>q. M q \<Longrightarrow> q \<in> Y \<longleftrightarrow> psnd q = \<langle>pfst q, t x (pfst q)\<rangle>"
      by (rule dfnE) blast
    have Y: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Y \<longleftrightarrow> v = \<langle>u, t x u\<rangle>)" using Y0 by simp
    show ?thesis
    proof (rule set_image[OF _ Y])
      show "M (f x)" using f x by (simp add: dfun_def)
    next
      show "M \<langle>u, t x u\<rangle>" for u by simp
    next
      show "p \<in> (\<lambda>y\<in>f x. t x y) \<longleftrightarrow> (\<exists>u. u \<in> f x \<and> p = \<langle>u, t x u\<rangle>)" for p
        using mem_Lam[OF tx, of p "f x"] by (auto dest: mem_M)
    qed
  qed
  ultimately show ?thesis by (simp add: dfun_def)
qed

lemma dfun_sep [dfn_rules]:
  "dfun f \<Longrightarrow> dfn (\<lambda>p. P (pfst p) (psnd p)) \<Longrightarrow> dfun (\<lambda>x. \<lbrace>y. y \<in> f x \<and> P x y\<rbrace>)"
proof -
  assume f: "dfun f" and P: "dfn (\<lambda>p. P (pfst p) (psnd p))"
  have "dcls (\<lambda>x. \<lbrace>y. y \<in> f x \<and> P x y\<rbrace>)" using f P by dfn
  moreover have "M \<lbrace>y. y \<in> f x \<and> P x y\<rbrace>" if x: "M x" for x
  proof (rule set_subset[of "f x"])
    show "M (f x)" using f x by (simp add: dfun_def)
  next
    have "dfn (\<lambda>y. y \<in> f x \<and> P x y)" using dfn_section[OF P x] by dfn
    then show "z \<in> f x" if "z \<in> \<lbrace>y. y \<in> f x \<and> P x y\<rbrace>" for z using that by (simp add: Coll_iff)
  qed
  ultimately show ?thesis by (simp add: dfun_def)
qed

end