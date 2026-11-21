section \<open>The axioms of NBG\<close>

theory Axioms
  imports Notation
begin

text \<open>
  Von Neumann--Bernays--Gödel set theory, following Mendelson, \<^emph>\<open>Introduction to
  Mathematical Logic\<close>, Chapter 4. There is one sort, classes, and one primitive, membership.
  A set is a class that is a member of some class.

  This file is the whole trusted base. Everything in it is a first-order statement about
  \<open>\<in>\<close>: the only constant that is axiomatized is membership, and every axiom is a closed
  formula whose quantifiers range over classes. Unordered and ordered pairs are introduced by
  definite description, because axioms B1 and B4--B7 and replacement mention ordered pairs.

  Comprehension is \<^emph>\<open>not\<close> an axiom scheme. Classes exist only when B1--B7 produce them, which
  is what makes this NBG and not Morse--Kelley: a formula that quantifies over classes does not
  define a class.

  There is no axiom of choice here, and neither infinity nor regularity; those two are stated
  in \<open>Axioms_Rest\<close>, which the development does not import.
\<close>

typedecl cls

axiomatization mem :: "cls \<Rightarrow> cls \<Rightarrow> bool"  (infix \<open>\<in>\<close> 50)

abbreviation not_mem :: "cls \<Rightarrow> cls \<Rightarrow> bool"  (infix \<open>\<notin>\<close> 50)
  where "x \<notin> A \<equiv> \<not> x \<in> A"

text \<open>\<open>M X\<close>: the class \<open>X\<close> is a set.\<close>

definition M :: "cls \<Rightarrow> bool"
  where "M X \<longleftrightarrow> (\<exists>Y. X \<in> Y)"

axiomatization where
  extensionality: "\<forall>X Y. (\<forall>z. z \<in> X \<longleftrightarrow> z \<in> Y) \<longrightarrow> X = Y" and
  pairing: "\<forall>x y. M x \<longrightarrow> M y \<longrightarrow> (\<exists>z. M z \<and> (\<forall>u. u \<in> z \<longleftrightarrow> u = x \<or> u = y))" and
  empty_set: "\<exists>x. M x \<and> (\<forall>y. y \<notin> x)"

text \<open>
  \<open>upair x y\<close> is the class of all sets equal to \<open>x\<close> or to \<open>y\<close>. For sets \<open>x\<close> and \<open>y\<close> it is the
  set that the pairing axiom provides. The description is total: when \<open>x\<close> is a proper class
  the result is \<open>{y}\<close>, or the empty class if \<open>y\<close> is proper too.
\<close>

definition upair :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "upair x y = (THE z. \<forall>u. u \<in> z \<longleftrightarrow> M u \<and> (u = x \<or> u = y))"

definition opair :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (\<open>(\<open>indent=1 notation=\<open>mixfix ordered pair\<close>\<close>\<langle>_,/ _\<rangle>)\<close>)
  where "\<langle>x, y\<rangle> = upair (upair x x) (upair x y)"

text \<open>
  The class existence axioms B1--B7. Lower-case variables are sets, and each is guarded by \<open>M\<close>
  wherever it occurs inside an ordered pair.
\<close>

axiomatization where
  B1: "\<exists>X. \<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> X \<longleftrightarrow> u \<in> v)" and
  B2: "\<forall>X Y. \<exists>Z. \<forall>u. u \<in> Z \<longleftrightarrow> u \<in> X \<and> u \<in> Y" and
  B3: "\<forall>X. \<exists>Z. \<forall>u. M u \<longrightarrow> (u \<in> Z \<longleftrightarrow> u \<notin> X)" and
  B4: "\<forall>X. \<exists>Z. \<forall>u. M u \<longrightarrow> (u \<in> Z \<longleftrightarrow> (\<exists>v. M v \<and> \<langle>u, v\<rangle> \<in> X))" and
  B5: "\<forall>X. \<exists>Z. \<forall>u v. M u \<longrightarrow> M v \<longrightarrow> (\<langle>u, v\<rangle> \<in> Z \<longleftrightarrow> u \<in> X)" and
  B6: "\<forall>X. \<exists>Z. \<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<langle>v, w\<rangle>, u\<rangle> \<in> X)" and
  B7: "\<forall>X. \<exists>Z. \<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> (\<langle>\<langle>u, v\<rangle>, w\<rangle> \<in> Z \<longleftrightarrow> \<langle>\<langle>u, w\<rangle>, v\<rangle> \<in> X)"

text \<open>The axioms that make sets: sum set, power set, subsets and replacement.\<close>

axiomatization where
  sum_set: "\<forall>x. M x \<longrightarrow> (\<exists>y. M y \<and> (\<forall>u. u \<in> y \<longleftrightarrow> (\<exists>v. u \<in> v \<and> v \<in> x)))" and
  power_set: "\<forall>x. M x \<longrightarrow> (\<exists>y. M y \<and> (\<forall>u. M u \<longrightarrow> (u \<in> y \<longleftrightarrow> (\<forall>w. w \<in> u \<longrightarrow> w \<in> x))))" and
  subsets: "\<forall>x Y. M x \<longrightarrow> (\<exists>z. M z \<and> (\<forall>u. u \<in> z \<longleftrightarrow> u \<in> x \<and> u \<in> Y))" and
  replacement:
    "\<forall>Y x. M x \<longrightarrow>
      (\<forall>u v w. M u \<longrightarrow> M v \<longrightarrow> M w \<longrightarrow> \<langle>u, v\<rangle> \<in> Y \<longrightarrow> \<langle>u, w\<rangle> \<in> Y \<longrightarrow> v = w) \<longrightarrow>
      (\<exists>y. M y \<and> (\<forall>v. M v \<longrightarrow> (v \<in> y \<longleftrightarrow> (\<exists>u. u \<in> x \<and> \<langle>u, v\<rangle> \<in> Y))))"

end
