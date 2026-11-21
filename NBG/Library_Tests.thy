section \<open>Tests of the library\<close>

theory Library_Tests
  imports Library
begin

text \<open>
  The library on the shapes the category theory produces: the components of a structure with
  six tagged components (as \<open>mkcat\<close> builds), a \<open>\<lambda>\<close> evaluated on a pair, and memberships in
  nested comprehensions.
\<close>

text \<open>Each component comes back by \<open>simp\<close>, and the structure is a set iff all six are.\<close>

lemma
  fixes obs arrs s t i c :: cls
  defines "S \<equiv> tag l0 obs \<union> tag l1 arrs \<union> tag l2 s \<union> tag l3 t \<union> tag l4 i \<union> tag l5 c"
  shows "cmp l0 S = obs" and "cmp l1 S = arrs" and "cmp l2 S = s"
    and "cmp l3 S = t" and "cmp l4 S = i" and "cmp l5 S = c"
    and "M S \<longleftrightarrow> M obs \<and> M arrs \<and> M s \<and> M t \<and> M i \<and> M c"
  unfolding S_def by simp_all

text \<open>A component that is a \<open>\<lambda>\<close>, read off the structure and applied, as \<open>src\<^bsub>C\<^esub> f\<close> is.\<close>

lemma
  fixes Obs Arrs :: cls
  defines "C \<equiv> tag l0 Obs \<union> tag l1 Arrs \<union> tag l2 (\<lambda>a\<in>Arrs. pfst (pfst a)) \<union> tag l3 (\<lambda>a\<in>Arrs. psnd (pfst a))"
  assumes "f \<in> Arrs"
  shows "cmp l2 C \<cdot> f = pfst (pfst f)" and "cmp l3 C \<cdot> f = psnd (pfst f)"
  using assms unfolding C_def by simp_all

text \<open>A \<open>\<lambda>\<close> on a product, evaluated on a pair: the hypotheses are only that the pair is in the domain.\<close>

lemma
  assumes "x \<in> A" and "y \<in> B"
  shows "(\<lambda>u\<in>A \<times> B. \<langle>psnd u, pfst u\<rangle>) \<cdot> \<langle>x, y\<rangle> = \<langle>y, x\<rangle>"
  using assms by (simp add: mem_M)

lemma
  assumes "x \<in> A" and "y \<in> B"
  shows "(\<lambda>u\<in>A \<times> B. F \<cdot> pfst u \<cdot> (G \<cdot> psnd u)) \<cdot> \<langle>x, y\<rangle> = F \<cdot> x \<cdot> (G \<cdot> y)"
  using assms by (simp add: mem_M)

text \<open>A canonical function is evaluated by \<open>simp\<close>, and two of them are equal iff they agree.\<close>

lemma "x \<in> A \<Longrightarrow> (\<lambda>u\<in>A. F \<cdot> u) \<cdot> x = F \<cdot> x"
  by simp

lemma "(\<lambda>u\<in>A. F \<cdot> u) = (\<lambda>u\<in>A. G \<cdot> u) \<longleftrightarrow> (\<forall>u. u \<in> A \<longrightarrow> F \<cdot> u = G \<cdot> u)"
  by (rule Lam_eq_iff) simp_all

text \<open>Memberships in nested comprehensions unfold by \<open>simp\<close> and are decided by \<open>auto\<close>.\<close>

lemma
  assumes "M a" and "M b"
  shows "\<langle>a, b\<rangle> \<in> \<lbrace>p. \<exists>\<^sub>s x y. p = \<langle>x, y\<rangle> \<and> x \<in> \<lbrace>u. u \<in> A \<and> u \<notin> B\<rbrace> \<and> y \<in> cdom R\<rbrace> \<longleftrightarrow>
    a \<in> A \<and> a \<notin> B \<and> (\<exists>\<^sub>s z. \<langle>b, z\<rangle> \<in> R)"
  using assms by auto

lemma
  assumes "x \<in> A"
  shows "x \<in> \<lbrace>v. \<exists>\<^sub>s w. w \<in> \<lbrace>z. \<exists>\<^sub>s y. y \<in> A \<and> z = sng y\<rbrace> \<and> v \<in> w\<rbrace>"
proof -
  have "sng x \<in> \<lbrace>z. \<exists>\<^sub>s y. y \<in> A \<and> z = sng y\<rbrace>"
    using assms by (auto simp: mem_M)
  moreover have "x \<in> sng x"
    using assms by (simp add: mem_M)
  ultimately have "\<exists>\<^sub>s w. w \<in> \<lbrace>z. \<exists>\<^sub>s y. y \<in> A \<and> z = sng y\<rbrace> \<and> x \<in> w"
    using M_sng by blast
  then show ?thesis
    using assms by (simp add: mem_M)
qed

text \<open>A comprehension in the shape of \<open>Hom C x y\<close>, with the maps read off a structure.\<close>

lemma
  fixes C :: cls
  defines "H \<equiv> \<lambda>x y. \<lbrace>f. f \<in> cmp l1 C \<and> cmp l2 C \<cdot> f = x \<and> cmp l3 C \<cdot> f = y\<rbrace>"
  shows "f \<in> H x y \<longleftrightarrow> f \<in> cmp l1 C \<and> cmp l2 C \<cdot> f = x \<and> cmp l3 C \<cdot> f = y"
  unfolding H_def by auto

text \<open>Sethood of a \<open>\<lambda>\<close> on a set, and of the image of a set.\<close>

lemma "M A \<Longrightarrow> M (\<lambda>u\<in>A. \<langle>u, F \<cdot> u\<rangle>)"
  by simp

lemma "M A \<Longrightarrow> M \<lbrace>y. \<exists>\<^sub>s x. x \<in> A \<and> y = F \<cdot> x\<rbrace>"
  by (rule M_replace) simp_all

end
