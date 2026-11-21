section \<open>Tests of the class existence method\<close>

theory Tests
  imports Classes
begin

text \<open>
  Goals the method \<open>dfn\<close> must prove, and one it must not. They are the shapes that the
  definitions of categories, diagrams and presheaf morphisms produce.
\<close>

lemma "dfn (\<lambda>p. \<exists>\<^sub>s x y. p = \<langle>x, y\<rangle> \<and> x \<in> A \<and> y \<in> B)"
  by dfn

lemma "dfn (\<lambda>u. \<exists>\<^sub>s v. \<langle>u, v\<rangle> \<in> X)"
  by dfn

lemma "M a \<Longrightarrow> dfn (\<lambda>x. \<forall>\<^sub>s y. y \<in> x \<longrightarrow> F \<cdot> \<langle>y, a\<rangle> = G \<cdot> (pfst x \<cdot> y))"
  by dfn

lemma "dfun f \<Longrightarrow> dcls T \<Longrightarrow> dfn (\<lambda>x. \<exists>\<^sub>s y. y \<in> T x \<and> (\<forall>\<^sub>s z. z \<in> f x \<longrightarrow> \<langle>z, y\<rangle> \<in> T x \<cdot> z))"
  by dfn

lemma "dcls T \<Longrightarrow> dfn (\<lambda>x. \<forall>\<^sub>s f g. f \<in> cmp l1 (T x) \<longrightarrow> g \<in> cmp l1 (T x) \<longrightarrow>
    cmp l5 (T x) \<cdot> \<langle>f, g\<rangle> \<in> cmp l1 (T x))"
  by dfn

lemma "dfun (\<lambda>X. \<langle>\<langle>X, X\<rangle>, \<lambda>j\<in>cmp l0 (pfst X). C \<cdot> (psnd X \<cdot> j)\<rangle>)"
  by dfn

lemma "dfn (\<lambda>w. \<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> b \<cdot> k \<and>
    (\<forall>\<^sub>s S. (\<forall>\<^sub>s u v. \<langle>u, v\<rangle> \<in> E \<longrightarrow> (u \<in> S \<longleftrightarrow> v \<in> S)) \<longrightarrow> \<langle>l, C \<cdot> \<langle>g, f\<rangle>\<rangle> \<in> S \<longrightarrow> w \<in> S))"
  by dfn

text \<open>A quantifier over classes: the method must fail, and it does.\<close>

ML \<open>
  val impredicative = Goal.init \<^cprop>\<open>dfn (\<lambda>x. \<exists>Y. x \<in> Y \<and> Y \<in> A)\<close>;
  val _ = \<^assert> (is_none (Seq.pull (Dfn.tac \<^context> 1 impredicative)));
\<close>

end
