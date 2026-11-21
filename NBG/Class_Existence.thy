section \<open>The Class Existence Theorem, from the axioms alone\<close>

theory Class_Existence
  imports Axioms
begin

text \<open>
  This theory proves, from extensionality, pairing, the empty set and B1--B7, that every
  formula built from membership atoms, negation, conjunction and quantifiers over sets defines
  a class. It is Mendelson's Class Existence Theorem. The formulas are a small datatype \<open>form\<close>
  with de Bruijn variables, evaluated in a list of sets; nothing here mentions the vocabulary of
  \<open>Classes\<close>, which uses the theorem in its one- and two-variable forms \<open>form_cls1\<close> and
  \<open>form_cls2\<close>. The last group of lemmas says which classes the set axioms make sets.

  None of the facts here carries a \<open>simp\<close> or \<open>intro\<close> attribute, so that importing this theory
  leaves the simplifier and the rule sets of \<open>Classes\<close> as they were.
\<close>

subsection \<open>First facts: sets, unordered and ordered pairs\<close>

lemma extensional: "(\<And>z. z \<in> X \<longleftrightarrow> z \<in> Y) \<Longrightarrow> X = Y"
  using extensionality by blast

lemma member_set: "x \<in> A \<Longrightarrow> M x"
  unfolding M_def by blast

text \<open>Two classes are equal when they have the same sets as members, and every member is a set.\<close>

lemma eq_iff_members: "(\<forall>w. M w \<longrightarrow> (w \<in> y \<longleftrightarrow> w \<in> B)) \<longleftrightarrow> y = B"
  using extensional member_set by blast

lemma empty_exists: "\<exists>e. M e \<and> (\<forall>u. u \<notin> e)"
  using empty_set by blast

lemma upair_exists: "\<exists>z. M z \<and> (\<forall>u. u \<in> z \<longleftrightarrow> M u \<and> (u = x \<or> u = y))"
proof (cases "M x"; cases "M y")
  assume "M x" "M y"
  then obtain z where "M z" "\<forall>u. u \<in> z \<longleftrightarrow> u = x \<or> u = y" using pairing by blast
  then have "\<forall>u. u \<in> z \<longleftrightarrow> M u \<and> (u = x \<or> u = y)" using \<open>M x\<close> \<open>M y\<close> by auto
  then show ?thesis using \<open>M z\<close> by blast
next
  assume "M x" "\<not> M y"
  then obtain z where "M z" "\<forall>u. u \<in> z \<longleftrightarrow> u = x \<or> u = x" using pairing by blast
  then have "\<forall>u. u \<in> z \<longleftrightarrow> M u \<and> (u = x \<or> u = y)" using \<open>M x\<close> \<open>\<not> M y\<close> by auto
  then show ?thesis using \<open>M z\<close> by blast
next
  assume "\<not> M x" "M y"
  then obtain z where "M z" "\<forall>u. u \<in> z \<longleftrightarrow> u = y \<or> u = y" using pairing by blast
  then have "\<forall>u. u \<in> z \<longleftrightarrow> M u \<and> (u = x \<or> u = y)" using \<open>M y\<close> \<open>\<not> M x\<close> by auto
  then show ?thesis using \<open>M z\<close> by blast
next
  assume "\<not> M x" "\<not> M y"
  then show ?thesis using empty_set by blast
qed

lemma upair_char: "M (upair x y) \<and> (\<forall>u. u \<in> upair x y \<longleftrightarrow> M u \<and> (u = x \<or> u = y))"
proof -
  obtain z where z: "M z" "\<forall>u. u \<in> z \<longleftrightarrow> M u \<and> (u = x \<or> u = y)"
    using upair_exists by blast
  have "upair x y = z"
    unfolding upair_def
  proof (rule the_equality)
    show "\<forall>u. u \<in> z \<longleftrightarrow> M u \<and> (u = x \<or> u = y)" by (fact z(2))
  next
    fix w assume "\<forall>u. u \<in> w \<longleftrightarrow> M u \<and> (u = x \<or> u = y)"
    then show "w = z" using z(2) by (blast intro: extensional)
  qed
  then show ?thesis using z by simp
qed

lemma upair_set: "M (upair x y)"
  using upair_char by blast

lemma upair_iff: "u \<in> upair x y \<longleftrightarrow> M u \<and> (u = x \<or> u = y)"
  using upair_char by blast

lemma opair_set: "M \<langle>x, y\<rangle>"
  unfolding opair_def by (rule upair_set)

lemma upair_eq_sets:
  assumes "M a" "M b" "M c" "M d" "upair a b = upair c d"
  shows "(a = c \<and> b = d) \<or> (a = d \<and> b = c)"
proof -
  have "a \<in> upair a b" "b \<in> upair a b" "c \<in> upair c d" "d \<in> upair c d"
    using assms(1-4) by (simp_all add: upair_iff)
  then have "a \<in> upair c d" "b \<in> upair c d" "c \<in> upair a b" "d \<in> upair a b"
    using assms(5) by simp_all
  then have "a = c \<or> a = d" "b = c \<or> b = d" "c = a \<or> c = b" "d = a \<or> d = b"
    by (simp_all add: upair_iff)
  then show ?thesis by blast
qed

lemma sng_eq_upair:
  assumes "M a" "M b" "M c" "upair a a = upair b c"
  shows "a = b \<and> a = c"
  using upair_eq_sets[OF assms(1,1,2,3,4)] by blast

lemma opair_inject:
  assumes "M x" "M y" "M x'" "M y'" "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle>"
  shows "x = x' \<and> y = y'"
proof -
  have "(upair x x = upair x' x' \<and> upair x y = upair x' y') \<or>
      (upair x x = upair x' y' \<and> upair x y = upair x' x')"
    using assms(5) upair_eq_sets[OF upair_set upair_set upair_set upair_set] by (simp add: opair_def)
  then show ?thesis
  proof
    assume c: "upair x x = upair x' x' \<and> upair x y = upair x' y'"
    then have "x = x'" using sng_eq_upair[of x x' x'] assms(1,3) by blast
    moreover have "(x = x' \<and> y = y') \<or> (x = y' \<and> y = x')"
      using upair_eq_sets[of x y x' y'] assms(1-4) c by blast
    ultimately show ?thesis by blast
  next
    assume c: "upair x x = upair x' y' \<and> upair x y = upair x' x'"
    then have "x = x' \<and> x = y'" using sng_eq_upair[of x x' y'] assms(1,3,4) by blast
    moreover have "x' = x \<and> x' = y"
    proof -
      have "upair x' x' = upair x y" using c by simp
      then show ?thesis using sng_eq_upair[of x' x y] assms(1-3) by blast
    qed
    ultimately show ?thesis by blast
  qed
qed

subsection \<open>Classes of pairs and triples\<close>

text \<open>
  B1--B7 give classes that are only prescribed on ordered pairs or triples of sets. These lemmas
  derive the ones the theorem needs: the converse of a relation, the three cylinders over a
  binary relation inside a class of triples, and the identity relation.
\<close>

lemma cl_conv: "\<exists>Z. \<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, u\<rangle> \<in> X)"
proof -
  obtain Y1 where Y1: "\<forall>a b. M a \<longrightarrow> M b \<longrightarrow> (\<langle>a, b\<rangle> \<in> Y1 \<longleftrightarrow> a \<in> X)" using B5 by blast
  obtain Y2 where Y2: "\<forall>a b c. M a \<longrightarrow> M b \<longrightarrow> M c \<longrightarrow> (\<langle>\<langle>a, b\<rangle>, c\<rangle> \<in> Y2 \<longleftrightarrow> \<langle>\<langle>a, c\<rangle>, b\<rangle> \<in> Y1)"
    using B7 by blast
  obtain Y3 where Y3: "\<forall>a b c. M a \<longrightarrow> M b \<longrightarrow> M c \<longrightarrow> (\<langle>\<langle>a, b\<rangle>, c\<rangle> \<in> Y3 \<longleftrightarrow> \<langle>\<langle>b, c\<rangle>, a\<rangle> \<in> Y2)"
    using B6 by blast
  obtain Z where Z: "\<forall>s. M s \<longrightarrow> (s \<in> Z \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>s, w\<rangle> \<in> Y3))" using B4 by blast
  obtain e where e: "M e" using empty_set by blast
  have "\<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, u\<rangle> \<in> X" if uv: "M u" "M v" for u v
  proof -
    have "\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Y3 \<longleftrightarrow> \<langle>v, u\<rangle> \<in> X" if "M w" for w
      using Y1 Y2 Y3 uv that by (simp add: opair_set)
    moreover have "\<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Y3)"
      using Z opair_set by blast
    ultimately show ?thesis using e by blast
  qed
  then show ?thesis by blast
qed

lemma cl_snd: "\<exists>Z. \<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> v \<in> X)"
proof -
  obtain Y where Y: "\<forall>a b. M a \<longrightarrow> M b \<longrightarrow> (\<langle>a, b\<rangle> \<in> Y \<longleftrightarrow> a \<in> X)" using B5 by blast
  obtain Z where Z: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, u\<rangle> \<in> Y)" using cl_conv by blast
  have "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> v \<in> X)" using Y Z by simp
  then show ?thesis by blast
qed

text \<open>In a class of triples \<open>\<langle>\<langle>u, v\<rangle>, w\<rangle>\<close>: a condition on \<open>\<langle>u, w\<rangle>\<close>, and a condition on \<open>\<langle>v, w\<rangle>\<close>.\<close>

lemma cl_cyl_mid: "\<exists>Z. \<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>u, w\<rangle> \<in> X)"
proof -
  obtain Y where Y: "\<forall>a b. M a \<longrightarrow> M b \<longrightarrow> (\<langle>a, b\<rangle> \<in> Y \<longleftrightarrow> a \<in> X)" using B5 by blast
  obtain Z where Z: "\<forall>a b c. M a \<longrightarrow> M b \<longrightarrow> M c \<longrightarrow> (\<langle>\<langle>a, b\<rangle>, c\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<langle>a, c\<rangle>, b\<rangle> \<in> Y)"
    using B7 by blast
  have "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>u, w\<rangle> \<in> X)"
    using Y Z by (simp add: opair_set)
  then show ?thesis by blast
qed

lemma cl_cyl_snd: "\<exists>Z. \<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, w\<rangle> \<in> X)"
proof -
  obtain Y where Y: "\<forall>a b. M a \<longrightarrow> M b \<longrightarrow> (\<langle>a, b\<rangle> \<in> Y \<longleftrightarrow> a \<in> X)" using B5 by blast
  obtain Z where Z: "\<forall>a b c. M a \<longrightarrow> M b \<longrightarrow> M c \<longrightarrow> (\<langle>\<langle>a, b\<rangle>, c\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<langle>b, c\<rangle>, a\<rangle> \<in> Y)"
    using B6 by blast
  have "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, w\<rangle> \<in> X)"
    using Y Z by (simp add: opair_set)
  then show ?thesis by blast
qed

lemma cl_id: "\<exists>I. \<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> I \<longleftrightarrow> u = v)"
proof -
  obtain E where E: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> E \<longleftrightarrow> u \<in> v)" using B1 by blast
  obtain E' where E'0: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> E' \<longleftrightarrow> \<langle>v, u\<rangle> \<in> E)" using cl_conv by blast
  have E': "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> E' \<longleftrightarrow> v \<in> u)" using E E'0 by simp
  obtain A1 where A10: "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> A1 \<longleftrightarrow> \<langle>u, w\<rangle> \<in> E')"
    using cl_cyl_mid by blast
  obtain A2 where A20: "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> A2 \<longleftrightarrow> \<langle>v, w\<rangle> \<in> E')"
    using cl_cyl_snd by blast
  obtain N1 where N1: "\<forall>s. M s \<longrightarrow> (s \<in> N1 \<longleftrightarrow> s \<notin> A1)" using B3 by blast
  obtain N2 where N2: "\<forall>s. M s \<longrightarrow> (s \<in> N2 \<longleftrightarrow> s \<notin> A2)" using B3 by blast
  obtain D1 where D1: "\<forall>s. s \<in> D1 \<longleftrightarrow> s \<in> A1 \<and> s \<in> N2" using B2 by blast
  obtain D2 where D2: "\<forall>s. s \<in> D2 \<longleftrightarrow> s \<in> A2 \<and> s \<in> N1" using B2 by blast
  obtain K1 where K1: "\<forall>s. M s \<longrightarrow> (s \<in> K1 \<longleftrightarrow> s \<notin> D1)" using B3 by blast
  obtain K2 where K2: "\<forall>s. M s \<longrightarrow> (s \<in> K2 \<longleftrightarrow> s \<notin> D2)" using B3 by blast
  obtain K where K: "\<forall>s. s \<in> K \<longleftrightarrow> s \<in> K1 \<and> s \<in> K2" using B2 by blast
  obtain D where D: "\<forall>s. M s \<longrightarrow> (s \<in> D \<longleftrightarrow> s \<notin> K)" using B3 by blast
  obtain P where P: "\<forall>s. M s \<longrightarrow> (s \<in> P \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>s, w\<rangle> \<in> D))" using B4 by blast
  obtain I where I: "\<forall>s. M s \<longrightarrow> (s \<in> I \<longleftrightarrow> s \<notin> P)" using B3 by blast
  have "\<langle>u, v\<rangle> \<in> I \<longleftrightarrow> u = v" if uv: "M u" "M v" for u v
  proof -
    have "\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> D \<longleftrightarrow> \<not> (w \<in> u \<longleftrightarrow> w \<in> v)" if w: "M w" for w
    proof -
      let ?s = "\<langle>\<langle>u, v\<rangle>, w\<rangle>"
      have s: "M ?s" by (rule opair_set)
      have a1: "?s \<in> A1 \<longleftrightarrow> w \<in> u" using A10 E' uv w by (simp add: opair_set)
      have a2: "?s \<in> A2 \<longleftrightarrow> w \<in> v" using A20 E' uv w by (simp add: opair_set)
      have "?s \<in> D \<longleftrightarrow> (?s \<in> A1 \<and> ?s \<notin> A2) \<or> (?s \<in> A2 \<and> ?s \<notin> A1)"
        using D K K1 K2 D1 D2 N1 N2 s by auto
      then show ?thesis using a1 a2 by blast
    qed
    moreover have "\<langle>u, v\<rangle> \<in> I \<longleftrightarrow> \<not> (\<exists>w. M w \<and> \<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> D)"
      using I P opair_set by simp
    ultimately have "\<langle>u, v\<rangle> \<in> I \<longleftrightarrow> (\<forall>w. M w \<longrightarrow> (w \<in> u \<longleftrightarrow> w \<in> v))"
      by blast
    then show ?thesis by (simp add: eq_iff_members)
  qed
  then show ?thesis by blast
qed

subsection \<open>Tuples and the classes of tuples\<close>

text \<open>
  \<open>tup [y\<^sub>k, \<dots>, y\<^sub>1] x\<close> is the tuple \<open>\<langle>\<dots>\<langle>\<langle>x, y\<^sub>1\<rangle>, y\<^sub>2\<rangle>\<dots>, y\<^sub>k\<rangle>\<close>. It is the code of the
  environment \<open>[y\<^sub>k, \<dots>, y\<^sub>1, x]\<close>, whose head is the most recently bound variable. \<open>tdef n \<Phi>\<close>
  says that the tuples of length \<open>n + 1\<close> whose environment satisfies \<open>\<Phi>\<close> are the tuples in
  some class (the class may hold other sets too).
\<close>

primrec tup :: "cls list \<Rightarrow> cls \<Rightarrow> cls" where
  "tup [] x = x"
| "tup (y # ys) x = \<langle>tup ys x, y\<rangle>"

definition tdef :: "nat \<Rightarrow> (cls list \<Rightarrow> bool) \<Rightarrow> bool" where
  "tdef n \<Phi> \<longleftrightarrow> (\<exists>Z. \<forall>ys x. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow>
     (tup ys x \<in> Z \<longleftrightarrow> \<Phi> (ys @ [x])))"

lemma tup_set: "M x \<Longrightarrow> M (tup ys x)"
  by (cases ys) (simp_all add: opair_set)

lemma env_nth_set: "(\<forall>y\<in>set ys. M y) \<Longrightarrow> M x \<Longrightarrow> i \<le> length ys \<Longrightarrow> M ((ys @ [x]) ! i)"
  by (cases "i = length ys") (simp_all add: nth_append)

text \<open>The projection to the \<open>i\<close>-th variable of the environment, as a class of pairs.\<close>

lemma cl_proj:
  "i \<le> n \<Longrightarrow> \<exists>P. \<forall>ys x z. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow> M z \<longrightarrow>
     (\<langle>tup ys x, z\<rangle> \<in> P \<longleftrightarrow> z = (ys @ [x]) ! i)"
proof (induction n arbitrary: i)
  case 0
  obtain I where I: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> I \<longleftrightarrow> u = v)" using cl_id by blast
  have "\<langle>tup ys x, z\<rangle> \<in> I \<longleftrightarrow> z = (ys @ [x]) ! i"
    if "length ys = 0" "M x" "M z" for ys x z
  proof -
    have "ys = []" "i = 0" using that(1) \<open>i \<le> 0\<close> by simp_all
    then show ?thesis using I that(2,3) by auto
  qed
  then show ?case by blast
next
  case (Suc n)
  note IH = Suc.IH and le = Suc.prems
  show ?case
  proof (cases i)
    case 0
    obtain I where I: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> I \<longleftrightarrow> u = v)" using cl_id by blast
    obtain Z where Z: "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>v, w\<rangle> \<in> I)"
      using cl_cyl_snd by blast
    have "\<langle>tup ys x, z\<rangle> \<in> Z \<longleftrightarrow> z = (ys @ [x]) ! i"
      if ys: "length ys = Suc n" "\<forall>y\<in>set ys. M y" and x: "M x" and z: "M z" for ys x z
    proof -
      obtain y ys' where ys': "ys = y # ys'" using ys(1) by (cases ys) auto
      have y: "M y" using ys(2) ys' by simp
      have "\<langle>tup ys x, z\<rangle> = \<langle>\<langle>tup ys' x, y\<rangle>, z\<rangle>" using ys' by simp
      moreover have "\<langle>\<langle>tup ys' x, y\<rangle>, z\<rangle> \<in> Z \<longleftrightarrow> y = z"
        using Z I tup_set[OF x] y z by simp
      moreover have "(ys @ [x]) ! i = y" using ys' \<open>i = 0\<close> by simp
      ultimately show ?thesis by auto
    qed
    then show ?thesis by blast
  next
    case (Suc k)
    have "k \<le> n" using le \<open>i = Suc k\<close> by simp
    then obtain P where P: "\<forall>ys x z. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow> M z \<longrightarrow>
        (\<langle>tup ys x, z\<rangle> \<in> P \<longleftrightarrow> z = (ys @ [x]) ! k)"
      using IH by blast
    obtain Z where Z: "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>u, w\<rangle> \<in> P)"
      using cl_cyl_mid by blast
    have "\<langle>tup ys x, z\<rangle> \<in> Z \<longleftrightarrow> z = (ys @ [x]) ! i"
      if ys: "length ys = Suc n" "\<forall>y\<in>set ys. M y" and x: "M x" and z: "M z" for ys x z
    proof -
      obtain y ys' where ys': "ys = y # ys'" using ys(1) by (cases ys) auto
      have y: "M y" and ys'M: "\<forall>y\<in>set ys'. M y" and len: "length ys' = n"
        using ys ys' by simp_all
      have "\<langle>tup ys x, z\<rangle> = \<langle>\<langle>tup ys' x, y\<rangle>, z\<rangle>" using ys' by simp
      moreover have "\<langle>\<langle>tup ys' x, y\<rangle>, z\<rangle> \<in> Z \<longleftrightarrow> \<langle>tup ys' x, z\<rangle> \<in> P"
        using Z tup_set[OF x] y z by simp
      moreover have "\<langle>tup ys' x, z\<rangle> \<in> P \<longleftrightarrow> z = (ys' @ [x]) ! k"
        using P len ys'M x z by blast
      moreover have "(ys @ [x]) ! i = (ys' @ [x]) ! k" using ys' \<open>i = Suc k\<close> by simp
      ultimately show ?thesis by simp
    qed
    then show ?thesis by blast
  qed
qed

text \<open>The atoms: a variable in a class, and a pair of variables in a class.\<close>

lemma tdef_in: "i \<le> n \<Longrightarrow> tdef n (\<lambda>\<rho>. \<rho> ! i \<in> A)"
proof -
  assume "i \<le> n"
  then obtain P where P: "\<forall>ys x z. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow> M z \<longrightarrow>
      (\<langle>tup ys x, z\<rangle> \<in> P \<longleftrightarrow> z = (ys @ [x]) ! i)"
    using cl_proj by blast
  obtain Y where Y: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Y \<longleftrightarrow> v \<in> A)" using cl_snd by blast
  obtain W where W: "\<forall>s. s \<in> W \<longleftrightarrow> s \<in> P \<and> s \<in> Y" using B2 by blast
  obtain Z where Z: "\<forall>s. M s \<longrightarrow> (s \<in> Z \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>s, w\<rangle> \<in> W))" using B4 by blast
  have "tup ys x \<in> Z \<longleftrightarrow> (ys @ [x]) ! i \<in> A"
    if ys: "length ys = n" "\<forall>y\<in>set ys. M y" and x: "M x" for ys x
  proof -
    let ?t = "tup ys x" and ?a = "(ys @ [x]) ! i"
    have t: "M ?t" using x by (rule tup_set)
    have a: "M ?a" using env_nth_set ys x \<open>i \<le> n\<close> by blast
    have Pa: "\<langle>?t, w\<rangle> \<in> P \<longleftrightarrow> w = ?a" if "M w" for w using P ys x that by blast
    have "\<langle>?t, w\<rangle> \<in> W \<longleftrightarrow> w = ?a \<and> w \<in> A" if "M w" for w
      using W Y Pa t that by blast
    then have "?t \<in> Z \<longleftrightarrow> (\<exists>w. M w \<and> w = ?a \<and> w \<in> A)" using Z t by blast
    then show ?thesis using a by blast
  qed
  then show ?thesis unfolding tdef_def by blast
qed

lemma tdef_in2: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> tdef n (\<lambda>\<rho>. \<langle>\<rho> ! i, \<rho> ! j\<rangle> \<in> A)"
proof -
  assume ij: "i \<le> n" "j \<le> n"
  obtain P where P: "\<forall>ys x z. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow> M z \<longrightarrow>
      (\<langle>tup ys x, z\<rangle> \<in> P \<longleftrightarrow> z = (ys @ [x]) ! i)"
    using cl_proj ij(1) by blast
  obtain Q where Q: "\<forall>ys x z. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow> M z \<longrightarrow>
      (\<langle>tup ys x, z\<rangle> \<in> Q \<longleftrightarrow> z = (ys @ [x]) ! j)"
    using cl_proj ij(2) by blast
  obtain A' where A': "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> A' \<longleftrightarrow> \<langle>v, u\<rangle> \<in> A)" using cl_conv by blast
  obtain W1 where W1: "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> W1 \<longleftrightarrow> \<langle>u, w\<rangle> \<in> P)"
    using cl_cyl_mid by blast
  obtain W2 where W2: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> W2 \<longleftrightarrow> u \<in> Q)" using B5 by blast
  obtain W3 where W3: "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> W3 \<longleftrightarrow> \<langle>v, w\<rangle> \<in> A')"
    using cl_cyl_snd by blast
  obtain W12 where W12: "\<forall>s. s \<in> W12 \<longleftrightarrow> s \<in> W1 \<and> s \<in> W2" using B2 by blast
  obtain W where W: "\<forall>s. s \<in> W \<longleftrightarrow> s \<in> W12 \<and> s \<in> W3" using B2 by blast
  obtain D where D: "\<forall>s. M s \<longrightarrow> (s \<in> D \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>s, w\<rangle> \<in> W))" using B4 by blast
  obtain Z where Z: "\<forall>s. M s \<longrightarrow> (s \<in> Z \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>s, w\<rangle> \<in> D))" using B4 by blast
  have "tup ys x \<in> Z \<longleftrightarrow> \<langle>(ys @ [x]) ! i, (ys @ [x]) ! j\<rangle> \<in> A"
    if ys: "length ys = n" "\<forall>y\<in>set ys. M y" and x: "M x" for ys x
  proof -
    let ?t = "tup ys x" and ?a = "(ys @ [x]) ! i" and ?b = "(ys @ [x]) ! j"
    have t: "M ?t" using x by (rule tup_set)
    have a: "M ?a" and b: "M ?b" using env_nth_set ys x ij by blast+
    have Pa: "\<langle>?t, w\<rangle> \<in> P \<longleftrightarrow> w = ?a" if "M w" for w using P ys x that by blast
    have Qb: "\<langle>?t, w\<rangle> \<in> Q \<longleftrightarrow> w = ?b" if "M w" for w using Q ys x that by blast
    have Wab: "\<langle>\<langle>?t, b'\<rangle>, a'\<rangle> \<in> W \<longleftrightarrow> a' = ?a \<and> b' = ?b \<and> \<langle>a', b'\<rangle> \<in> A" if ab: "M a'" "M b'" for a' b'
    proof -
      have "\<langle>\<langle>?t, b'\<rangle>, a'\<rangle> \<in> W \<longleftrightarrow> \<langle>?t, a'\<rangle> \<in> P \<and> \<langle>?t, b'\<rangle> \<in> Q \<and> \<langle>b', a'\<rangle> \<in> A'"
        using W W12 W1 W2 W3 t ab by (simp add: opair_set)
      then show ?thesis using Pa Qb A' ab by simp
    qed
    have "\<langle>?t, b'\<rangle> \<in> D \<longleftrightarrow> b' = ?b \<and> \<langle>?a, b'\<rangle> \<in> A" if b': "M b'" for b'
    proof -
      have "\<langle>?t, b'\<rangle> \<in> D \<longleftrightarrow> (\<exists>a'. M a' \<and> \<langle>\<langle>?t, b'\<rangle>, a'\<rangle> \<in> W)" using D opair_set by blast
      also have "\<dots> \<longleftrightarrow> (\<exists>a'. M a' \<and> a' = ?a \<and> b' = ?b \<and> \<langle>a', b'\<rangle> \<in> A)" using Wab b' by blast
      also have "\<dots> \<longleftrightarrow> b' = ?b \<and> \<langle>?a, b'\<rangle> \<in> A" using a by blast
      finally show ?thesis .
    qed
    then have "?t \<in> Z \<longleftrightarrow> (\<exists>b'. M b' \<and> b' = ?b \<and> \<langle>?a, b'\<rangle> \<in> A)" using Z t by blast
    then show ?thesis using b by blast
  qed
  then show ?thesis unfolding tdef_def by blast
qed

lemma tdef_mem: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> tdef n (\<lambda>\<rho>. \<rho> ! i \<in> \<rho> ! j)"
proof -
  assume ij: "i \<le> n" "j \<le> n"
  obtain E where E: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> E \<longleftrightarrow> u \<in> v)" using B1 by blast
  have "tdef n (\<lambda>\<rho>. \<langle>\<rho> ! i, \<rho> ! j\<rangle> \<in> E)" using ij by (rule tdef_in2)
  then obtain Z where Z: "\<forall>ys x. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow>
      (tup ys x \<in> Z \<longleftrightarrow> \<langle>(ys @ [x]) ! i, (ys @ [x]) ! j\<rangle> \<in> E)"
    unfolding tdef_def by blast
  have "tup ys x \<in> Z \<longleftrightarrow> (ys @ [x]) ! i \<in> (ys @ [x]) ! j"
    if ys: "length ys = n" "\<forall>y\<in>set ys. M y" and x: "M x" for ys x
  proof -
    have "M ((ys @ [x]) ! i)" "M ((ys @ [x]) ! j)" using env_nth_set ys x ij by simp_all
    then show ?thesis using Z E ys x by simp
  qed
  then show ?thesis unfolding tdef_def by blast
qed

text \<open>The connectives and the quantifier over sets.\<close>

lemma tdef_not: "tdef n \<Phi> \<Longrightarrow> tdef n (\<lambda>\<rho>. \<not> \<Phi> \<rho>)"
proof -
  assume "tdef n \<Phi>"
  then obtain Z where Z: "\<forall>ys x. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow>
      (tup ys x \<in> Z \<longleftrightarrow> \<Phi> (ys @ [x]))" unfolding tdef_def by blast
  obtain Z' where Z': "\<forall>s. M s \<longrightarrow> (s \<in> Z' \<longleftrightarrow> s \<notin> Z)" using B3 by blast
  have "tup ys x \<in> Z' \<longleftrightarrow> \<not> \<Phi> (ys @ [x])"
    if ys: "length ys = n" "\<forall>y\<in>set ys. M y" and x: "M x" for ys x
    using Z Z' ys x tup_set[OF x] by simp
  then show ?thesis unfolding tdef_def by blast
qed

lemma tdef_conj: "tdef n \<Phi> \<Longrightarrow> tdef n \<Psi> \<Longrightarrow> tdef n (\<lambda>\<rho>. \<Phi> \<rho> \<and> \<Psi> \<rho>)"
proof -
  assume "tdef n \<Phi>" "tdef n \<Psi>"
  then obtain Z1 Z2 where
    Z1: "\<forall>ys x. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow> (tup ys x \<in> Z1 \<longleftrightarrow> \<Phi> (ys @ [x]))" and
    Z2: "\<forall>ys x. length ys = n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow> (tup ys x \<in> Z2 \<longleftrightarrow> \<Psi> (ys @ [x]))"
    unfolding tdef_def by blast
  obtain Z where Z: "\<forall>s. s \<in> Z \<longleftrightarrow> s \<in> Z1 \<and> s \<in> Z2" using B2 by blast
  have "tup ys x \<in> Z \<longleftrightarrow> \<Phi> (ys @ [x]) \<and> \<Psi> (ys @ [x])"
    if ys: "length ys = n" "\<forall>y\<in>set ys. M y" and x: "M x" for ys x
    using Z Z1 Z2 ys x by simp
  then show ?thesis unfolding tdef_def by blast
qed

lemma tdef_ex: "tdef (Suc n) \<Phi> \<Longrightarrow> tdef n (\<lambda>\<rho>. \<exists>y. M y \<and> \<Phi> (y # \<rho>))"
proof -
  assume "tdef (Suc n) \<Phi>"
  then obtain Z where Z: "\<forall>ys x. length ys = Suc n \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow>
      (tup ys x \<in> Z \<longleftrightarrow> \<Phi> (ys @ [x]))" unfolding tdef_def by blast
  obtain Z' where Z': "\<forall>s. M s \<longrightarrow> (s \<in> Z' \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>s, w\<rangle> \<in> Z))" using B4 by blast
  have "tup ys x \<in> Z' \<longleftrightarrow> (\<exists>y. M y \<and> \<Phi> (y # ys @ [x]))"
    if ys: "length ys = n" "\<forall>y\<in>set ys. M y" and x: "M x" for ys x
  proof -
    have "\<langle>tup ys x, y\<rangle> \<in> Z \<longleftrightarrow> \<Phi> (y # ys @ [x])" if y: "M y" for y
    proof -
      have "length (y # ys) = Suc n" "\<forall>y'\<in>set (y # ys). M y'" using ys y by simp_all
      then have "tup (y # ys) x \<in> Z \<longleftrightarrow> \<Phi> ((y # ys) @ [x])" using Z x by blast
      then show ?thesis by simp
    qed
    moreover have "tup ys x \<in> Z' \<longleftrightarrow> (\<exists>w. M w \<and> \<langle>tup ys x, w\<rangle> \<in> Z)"
      using Z' tup_set[OF x] by blast
    ultimately show ?thesis by blast
  qed
  then show ?thesis unfolding tdef_def by blast
qed

subsection \<open>Formulas\<close>

text \<open>
  The formulas of the theorem. Variables are de Bruijn indices into the environment; \<open>FEx\<close>
  binds index \<open>0\<close>. Class parameters enter only through the atoms \<open>FIn\<close> and \<open>FIn2\<close>.
\<close>

datatype form =
    FMem nat nat
  | FIn nat cls
  | FIn2 nat nat cls
  | FNot form
  | FAnd form form
  | FEx form

primrec feval :: "form \<Rightarrow> cls list \<Rightarrow> bool" where
  "feval (FMem i j) \<rho> = (\<rho> ! i \<in> \<rho> ! j)"
| "feval (FIn i A) \<rho> = (\<rho> ! i \<in> A)"
| "feval (FIn2 i j A) \<rho> = (\<langle>\<rho> ! i, \<rho> ! j\<rangle> \<in> A)"
| "feval (FNot \<phi>) \<rho> = (\<not> feval \<phi> \<rho>)"
| "feval (FAnd \<phi> \<psi>) \<rho> = (feval \<phi> \<rho> \<and> feval \<psi> \<rho>)"
| "feval (FEx \<phi>) \<rho> = (\<exists>y. M y \<and> feval \<phi> (y # \<rho>))"

text \<open>\<open>fbnd \<phi> n\<close>: the free variables of \<open>\<phi>\<close> are below \<open>n\<close>.\<close>

primrec fbnd :: "form \<Rightarrow> nat \<Rightarrow> bool" where
  "fbnd (FMem i j) n = (i < n \<and> j < n)"
| "fbnd (FIn i A) n = (i < n)"
| "fbnd (FIn2 i j A) n = (i < n \<and> j < n)"
| "fbnd (FNot \<phi>) n = fbnd \<phi> n"
| "fbnd (FAnd \<phi> \<psi>) n = (fbnd \<phi> n \<and> fbnd \<psi> n)"
| "fbnd (FEx \<phi>) n = fbnd \<phi> (Suc n)"

theorem form_tdef: "fbnd \<phi> (Suc n) \<Longrightarrow> tdef n (feval \<phi>)"
proof (induction \<phi> arbitrary: n)
  case (FMem i j)
  then show ?case using tdef_mem[of i n j] by simp
next
  case (FIn i A)
  then show ?case using tdef_in[of i n A] by simp
next
  case (FIn2 i j A)
  then show ?case using tdef_in2[of i n j A] by simp
next
  case (FNot \<phi>)
  then show ?case using tdef_not[of n "feval \<phi>"] by simp
next
  case (FAnd \<phi> \<psi>)
  then show ?case using tdef_conj[of n "feval \<phi>" "feval \<psi>"] by simp
next
  case (FEx \<phi>)
  then show ?case using tdef_ex[of n "feval \<phi>"] by simp
qed

text \<open>The theorem for one and for two variables, the forms in which \<open>Classes\<close> uses it.\<close>

lemma form_cls1: "fbnd \<phi> 1 \<Longrightarrow> \<exists>C. \<forall>x. M x \<longrightarrow> (x \<in> C \<longleftrightarrow> feval \<phi> [x])"
proof -
  assume "fbnd \<phi> 1"
  then have "tdef 0 (feval \<phi>)" by (intro form_tdef) simp
  then obtain Z where Z: "\<forall>ys x. length ys = 0 \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow>
      (tup ys x \<in> Z \<longleftrightarrow> feval \<phi> (ys @ [x]))"
    unfolding tdef_def by blast
  have "x \<in> Z \<longleftrightarrow> feval \<phi> [x]" if "M x" for x
  proof -
    have "tup [] x \<in> Z \<longleftrightarrow> feval \<phi> ([] @ [x])" using Z that by simp
    then show ?thesis by simp
  qed
  then show ?thesis by blast
qed

lemma form_cls2: "fbnd \<phi> 2 \<Longrightarrow> \<exists>C. \<forall>x z. M x \<longrightarrow> M z \<longrightarrow> (\<langle>x, z\<rangle> \<in> C \<longleftrightarrow> feval \<phi> [z, x])"
proof -
  assume "fbnd \<phi> 2"
  then have "tdef 1 (feval \<phi>)" by (intro form_tdef) (simp add: numeral_2_eq_2)
  then obtain Z where Z: "\<forall>ys x. length ys = 1 \<longrightarrow> (\<forall>y\<in>set ys. M y) \<longrightarrow> M x \<longrightarrow>
      (tup ys x \<in> Z \<longleftrightarrow> feval \<phi> (ys @ [x]))"
    unfolding tdef_def by blast
  have "\<langle>x, z\<rangle> \<in> Z \<longleftrightarrow> feval \<phi> [z, x]" if "M x" "M z" for x z
  proof -
    have "length [z] = 1" "\<forall>y\<in>set [z]. M y" using that by simp_all
    then have "tup [z] x \<in> Z \<longleftrightarrow> feval \<phi> ([z] @ [x])" using Z that(1) by blast
    then show ?thesis by simp
  qed
  then show ?thesis by blast
qed

subsection \<open>Derived formulas\<close>

text \<open>Disjunction, equivalence, the universal quantifier, and the formulas for equality, pairs.\<close>

definition FOr :: "form \<Rightarrow> form \<Rightarrow> form" where
  "FOr \<phi> \<psi> = FNot (FAnd (FNot \<phi>) (FNot \<psi>))"

definition FIff :: "form \<Rightarrow> form \<Rightarrow> form" where
  "FIff \<phi> \<psi> = FAnd (FOr (FNot \<phi>) \<psi>) (FOr (FNot \<psi>) \<phi>)"

definition FAll :: "form \<Rightarrow> form" where
  "FAll \<phi> = FNot (FEx (FNot \<phi>))"

definition FFalse :: form where
  "FFalse = FAnd (FMem 0 0) (FNot (FMem 0 0))"

definition FCst :: "bool \<Rightarrow> form" where
  "FCst b = (if b then FNot FFalse else FFalse)"

text \<open>\<open>FEqC i j R\<close>: the variable \<open>i\<close> is the section of \<open>R\<close> at the variable \<open>j\<close>.\<close>

definition FEqC :: "nat \<Rightarrow> nat \<Rightarrow> cls \<Rightarrow> form" where
  "FEqC i j R = FAll (FIff (FMem 0 (Suc i)) (FIn2 (Suc j) 0 R))"

definition FEq :: "nat \<Rightarrow> nat \<Rightarrow> form" where
  "FEq i j = FAll (FIff (FMem 0 (Suc i)) (FMem 0 (Suc j)))"

definition FUp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> form" where
  "FUp w a b = FAll (FIff (FMem 0 (Suc w)) (FOr (FEq 0 (Suc a)) (FEq 0 (Suc b))))"

definition FOp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> form" where
  "FOp q a b = FAll (FIff (FMem 0 (Suc q)) (FOr (FUp 0 (Suc a) (Suc a)) (FUp 0 (Suc a) (Suc b))))"

lemma feval_FOr: "feval (FOr \<phi> \<psi>) \<rho> = (feval \<phi> \<rho> \<or> feval \<psi> \<rho>)"
  by (simp add: FOr_def)

lemma feval_FIff: "feval (FIff \<phi> \<psi>) \<rho> = (feval \<phi> \<rho> \<longleftrightarrow> feval \<psi> \<rho>)"
  by (auto simp: FIff_def feval_FOr)

lemma feval_FAll: "feval (FAll \<phi>) \<rho> = (\<forall>y. M y \<longrightarrow> feval \<phi> (y # \<rho>))"
  by (simp add: FAll_def)

lemma feval_FCst: "feval (FCst b) \<rho> = b"
  by (simp add: FCst_def FFalse_def)

lemma feval_FEqC: "feval (FEqC i j R) \<rho> = (\<forall>w. M w \<longrightarrow> (w \<in> \<rho> ! i \<longleftrightarrow> \<langle>\<rho> ! j, w\<rangle> \<in> R))"
  by (simp add: FEqC_def feval_FAll feval_FIff)

lemma feval_FEq: "feval (FEq i j) \<rho> = (\<rho> ! i = \<rho> ! j)"
  by (simp add: FEq_def feval_FAll feval_FIff eq_iff_members)

lemma feval_FUp: "feval (FUp w a b) \<rho> = (\<rho> ! w = upair (\<rho> ! a) (\<rho> ! b))"
proof -
  have "feval (FUp w a b) \<rho> \<longleftrightarrow> (\<forall>y. M y \<longrightarrow> (y \<in> \<rho> ! w \<longleftrightarrow> y \<in> upair (\<rho> ! a) (\<rho> ! b)))"
    by (simp add: FUp_def feval_FAll feval_FIff feval_FOr feval_FEq upair_iff)
  then show ?thesis by (simp add: eq_iff_members)
qed

lemma feval_FOp: "feval (FOp q a b) \<rho> = (\<rho> ! q = \<langle>\<rho> ! a, \<rho> ! b\<rangle>)"
proof -
  have "feval (FOp q a b) \<rho> \<longleftrightarrow> (\<forall>y. M y \<longrightarrow> (y \<in> \<rho> ! q \<longleftrightarrow> y \<in> \<langle>\<rho> ! a, \<rho> ! b\<rangle>))"
    by (simp add: FOp_def opair_def feval_FAll feval_FIff feval_FOr feval_FUp upair_iff)
  then show ?thesis by (simp add: eq_iff_members)
qed

lemmas feval_simps = feval.simps feval_FOr feval_FIff feval_FAll feval_FCst feval_FEqC
  feval_FEq feval_FUp feval_FOp

lemma fbnd_derived:
  "fbnd (FOr \<phi> \<psi>) n = (fbnd \<phi> n \<and> fbnd \<psi> n)"
  "fbnd (FIff \<phi> \<psi>) n = (fbnd \<phi> n \<and> fbnd \<psi> n)"
  "fbnd (FAll \<phi>) n = fbnd \<phi> (Suc n)"
  "fbnd (FCst c) n = (0 < n)"
  "fbnd (FEqC i j R) n = (i < n \<and> j < n)"
  "fbnd (FEq i j) n = (i < n \<and> j < n)"
  "fbnd (FUp w a b) n = (w < n \<and> a < n \<and> b < n)"
  "fbnd (FOp q a b) n = (q < n \<and> a < n \<and> b < n)"
  by (auto simp: FOr_def FIff_def FAll_def FCst_def FFalse_def FEqC_def FEq_def FUp_def FOp_def)

lemmas fbnd_simps = fbnd.simps fbnd_derived

subsection \<open>Which classes are sets\<close>

text \<open>
  A subclass of a set is a set (subsets); so is a class inside the union of two sets (pairing
  and sum set), a class of ordered pairs from two sets (power set, twice), a class inside the
  union of the union of a set (sum set, twice), and the image of a set under a class function
  (replacement).
\<close>

lemma set_subset: "M a \<Longrightarrow> (\<And>z. z \<in> B \<Longrightarrow> z \<in> a) \<Longrightarrow> M B"
proof -
  assume a: "M a" and sub: "\<And>z. z \<in> B \<Longrightarrow> z \<in> a"
  obtain z where "M z" "\<forall>u. u \<in> z \<longleftrightarrow> u \<in> a \<and> u \<in> B" using subsets a by blast
  moreover have "z = B" using calculation sub by (blast intro: extensional)
  ultimately show ?thesis by simp
qed

lemma union_exists: "M a \<Longrightarrow> M b \<Longrightarrow> \<exists>c. M c \<and> (\<forall>u. u \<in> c \<longleftrightarrow> u \<in> a \<or> u \<in> b)"
proof -
  assume "M a" "M b"
  obtain c where "M c" "\<forall>u. u \<in> c \<longleftrightarrow> (\<exists>v. u \<in> v \<and> v \<in> upair a b)"
    using sum_set upair_set by blast
  then show ?thesis using \<open>M a\<close> \<open>M b\<close> by (auto simp: upair_iff)
qed

lemma set_union: "M a \<Longrightarrow> M b \<Longrightarrow> (\<And>z. z \<in> B \<Longrightarrow> z \<in> a \<or> z \<in> b) \<Longrightarrow> M B"
proof -
  assume "M a" "M b" and sub: "\<And>z. z \<in> B \<Longrightarrow> z \<in> a \<or> z \<in> b"
  then obtain c where "M c" "\<forall>u. u \<in> c \<longleftrightarrow> u \<in> a \<or> u \<in> b" using union_exists by blast
  then show ?thesis using set_subset[of c B] sub by blast
qed

lemma set_Union2: "M a \<Longrightarrow> (\<And>z. z \<in> B \<Longrightarrow> \<exists>v w. z \<in> v \<and> v \<in> w \<and> w \<in> a) \<Longrightarrow> M B"
proof -
  assume a: "M a" and sub: "\<And>z. z \<in> B \<Longrightarrow> \<exists>v w. z \<in> v \<and> v \<in> w \<and> w \<in> a"
  obtain c where c: "M c" "\<forall>u. u \<in> c \<longleftrightarrow> (\<exists>v. u \<in> v \<and> v \<in> a)" using sum_set a by blast
  obtain d where d: "M d" "\<forall>u. u \<in> d \<longleftrightarrow> (\<exists>v. u \<in> v \<and> v \<in> c)" using sum_set c(1) by blast
  show ?thesis using set_subset[OF d(1)] sub c(2) d(2) by blast
qed

lemma pow_exists: "M a \<Longrightarrow> \<exists>p. M p \<and> (\<forall>u. M u \<longrightarrow> (u \<in> p \<longleftrightarrow> (\<forall>w. w \<in> u \<longrightarrow> w \<in> a)))"
  using power_set by blast

lemma set_pairs:
  "M a \<Longrightarrow> M b \<Longrightarrow> (\<And>p. p \<in> B \<Longrightarrow> \<exists>u v. u \<in> a \<and> v \<in> b \<and> p = \<langle>u, v\<rangle>) \<Longrightarrow> M B"
proof -
  assume a: "M a" and b: "M b" and sub: "\<And>p. p \<in> B \<Longrightarrow> \<exists>u v. u \<in> a \<and> v \<in> b \<and> p = \<langle>u, v\<rangle>"
  obtain c where c: "M c" "\<forall>u. u \<in> c \<longleftrightarrow> u \<in> a \<or> u \<in> b" using union_exists a b by blast
  obtain p1 where p1: "M p1" "\<forall>u. M u \<longrightarrow> (u \<in> p1 \<longleftrightarrow> (\<forall>w. w \<in> u \<longrightarrow> w \<in> c))"
    using pow_exists c(1) by blast
  obtain p2 where p2: "M p2" "\<forall>u. M u \<longrightarrow> (u \<in> p2 \<longleftrightarrow> (\<forall>w. w \<in> u \<longrightarrow> w \<in> p1))"
    using pow_exists p1(1) by blast
  have "\<langle>u, v\<rangle> \<in> p2" if "u \<in> a" "v \<in> b" for u v
  proof -
    have "upair u u \<in> p1" "upair u v \<in> p1"
      using p1 c that by (auto simp: upair_set upair_iff)
    then show ?thesis
      using p2 by (auto simp: opair_def upair_set upair_iff)
  qed
  then show ?thesis using set_subset[OF p2(1)] sub by blast
qed

lemma set_image:
  assumes a: "M a"
    and Y: "\<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Y \<longleftrightarrow> v = F u)"
    and F: "\<And>u. M u \<Longrightarrow> M (F u)"
    and B: "\<And>p. p \<in> B \<longleftrightarrow> (\<exists>u. u \<in> a \<and> p = F u)"
  shows "M B"
proof -
  have "\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> \<langle>u, v\<rangle> \<in> Y \<longrightarrow> \<langle>u, w\<rangle> \<in> Y \<longrightarrow> v = w"
    using Y by auto
  then obtain y where y: "M y" "\<forall>v. M v \<longrightarrow> (v \<in> y \<longleftrightarrow> (\<exists>u. u \<in> a \<and> \<langle>u, v\<rangle> \<in> Y))"
    using replacement a by blast
  have "B = y"
  proof (rule extensional)
    fix p
    show "p \<in> B \<longleftrightarrow> p \<in> y"
    proof
      assume "p \<in> B"
      then obtain u where u: "u \<in> a" "p = F u" using B by blast
      then have "M u" "M p" using member_set F by blast+
      then have "\<langle>u, p\<rangle> \<in> Y" using Y u(2) by blast
      then show "p \<in> y" using y(2) u(1) \<open>M p\<close> by blast
    next
      assume "p \<in> y"
      then have "M p" by (rule member_set)
      then obtain u where u: "u \<in> a" "\<langle>u, p\<rangle> \<in> Y" using y(2) \<open>p \<in> y\<close> by blast
      then have "p = F u" using Y member_set \<open>M p\<close> by blast
      then show "p \<in> B" using B u(1) by blast
    qed
  qed
  then show ?thesis using y(1) by simp
qed

declare tup.simps [simp del] feval.simps [simp del] fbnd.simps [simp del]

end