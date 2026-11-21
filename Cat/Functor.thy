section \<open>Functors: identities, composites, canonical representatives\<close>

theory Functor
  imports Category
begin

text \<open>
  General facts about functors as classes: the identity functor and composites are functors,
  they are canonical, and composition is associative and unital on canonical functors.
\<close>

subsection \<open>Sethood\<close>

text \<open>
  A structure is a set exactly when its components are, so every component of a small category
  or of a functor that is a set is a set. The identity functor and composites out of a small
  category are sets, and a small category is locally small: each hom-class is a subclass of the
  set of arrows.
\<close>

lemma M_mkfun_iff [simp]: "M (mkfun a b) \<longleftrightarrow> M a \<and> M b"
  by (simp add: mkfun_def)

lemma M_mkfun: "M a \<Longrightarrow> M b \<Longrightarrow> M (mkfun a b)"
  by simp

lemma M_mkcat_iff [simp]:
  "M (mkcat obs arrs s t i c) \<longleftrightarrow> M obs \<and> M arrs \<and> M s \<and> M t \<and> M i \<and> M c"
  by (simp add: mkcat_def)

lemma M_mkcat: "M obs \<Longrightarrow> M arrs \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> M i \<Longrightarrow> M c \<Longrightarrow> M (mkcat obs arrs s t i c)"
  by simp

lemma M_Ob [simp]: "M C \<Longrightarrow> M (Ob C)" by (simp add: Ob_def)
lemma M_Arr [simp]: "M C \<Longrightarrow> M (Arr C)" by (simp add: Arr_def)
lemma M_Src [simp]: "M C \<Longrightarrow> M (Src C)" by (simp add: Src_def)
lemma M_Tgt [simp]: "M C \<Longrightarrow> M (Tgt C)" by (simp add: Tgt_def)
lemma M_Idt [simp]: "M C \<Longrightarrow> M (Idt C)" by (simp add: Idt_def)
lemma M_Cmp [simp]: "M C \<Longrightarrow> M (Cmp C)" by (simp add: Cmp_def)
lemma M_FOb [simp]: "M F \<Longrightarrow> M (FOb F)" by (simp add: FOb_def)
lemma M_FArr [simp]: "M F \<Longrightarrow> M (FArr F)" by (simp add: FArr_def)

lemma M_idf [simp]: "M C \<Longrightarrow> M (idf C)"
  by (simp add: idf_def)

lemma M_fcomp [simp]: "M C \<Longrightarrow> M (fcomp C G F)"
  by (simp add: fcomp_def)

lemma small_locally_small:
  assumes "M C"
  shows "locally_small C"
proof -
  have "M (Hom C x y)" for x y
  proof (rule M_subcls)
    show "M (Arr C)"
      using assms by simp
    show "Hom C x y \<subseteq> Arr C"
      by auto
  qed
  then show ?thesis
    unfolding locally_small_def by blast
qed

subsection \<open>Identity laws up to an equation\<close>

text \<open>
  The simplifier rewrites \<open>tgt\<^bsub>C\<^esub> f\<close> before it tries \<open>cat_id_left\<close>, so that rule rarely fires on
  \<open>id\<^bsub>C\<^esub> y \<circ>\<^bsub>C\<^esub> f\<close> where \<open>y\<close> is \<open>tgt\<^bsub>C\<^esub> f\<close> in another form. These forms take the equation as a
  condition, which the simplifier proves.
\<close>

lemma cat_id_left_eq [simp]:
  "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> tgt\<^bsub>C\<^esub> f = y \<Longrightarrow> id\<^bsub>C\<^esub> y \<circ>\<^bsub>C\<^esub> f = f"
  by (drule sym) simp

lemma cat_id_right_eq [simp]:
  "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> f = x \<Longrightarrow> f \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> x = f"
  by (drule sym) simp

subsection \<open>Canonical functors\<close>

text \<open>
  The two halves of \<open>strict_functor\<close>, and the fact that a canonical functor out of a small
  category is a set.
\<close>

lemma strict_functorI:
  "is_functor F C D \<Longrightarrow> F = mkfun (\<lambda>x\<in>Ob C. F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. F \<cdot>\<^sub>a f) \<Longrightarrow> strict_functor F C D"
  by (simp add: strict_functor_def)

lemma strict_functor_functor: "strict_functor F C D \<Longrightarrow> is_functor F C D"
  by (simp add: strict_functor_def)

lemma strict_functor_canonical:
  "strict_functor F C D \<Longrightarrow> F = mkfun (\<lambda>x\<in>Ob C. F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. F \<cdot>\<^sub>a f)"
  by (simp add: strict_functor_def)

lemma M_strict_functor:
  assumes "M C" and "strict_functor F C D"
  shows "M F"
proof -
  have "M (mkfun (\<lambda>x\<in>Ob C. F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. F \<cdot>\<^sub>a f))"
    using \<open>M C\<close> by simp
  then show ?thesis
    by (metis strict_functor_canonical[OF \<open>strict_functor F C D\<close>])
qed

subsection \<open>Identity and composite functors\<close>

text \<open>
  The identity of a category is a canonical functor, and so is the composite of two functors out
  of a category. Composition is associative, and the identities are its units on canonical
  functors. Every hypothesis \<open>category C\<close> below is needed: without it an arrow of \<open>C\<close> may have a
  source outside \<open>Ob C\<close>, or a composite outside \<open>Arr C\<close>, where \<open>idf\<close> and \<open>fcomp\<close> give \<open>\<emptyset>\<close>.
\<close>

lemma idf_functor:
  assumes "category C"
  shows "is_functor (idf C) C C"
  by (rule is_functorI) (simp_all add: assms)

lemma idf_strict:
  assumes "category C"
  shows "strict_functor (idf C) C C"
  using idf_functor[OF assms] idf_canonical by (rule strict_functorI)

lemma fcomp_functor:
  assumes "category C" and "is_functor F C D" and "is_functor G D E"
  shows "is_functor (fcomp C G F) C E"
proof (rule is_functorI)
  fix f g
  assume f: "f \<in> Arr C" and g: "g \<in> Arr C" and fg: "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f"
  have "F \<cdot>\<^sub>a (g \<circ>\<^bsub>C\<^esub> f) = F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f"
    using assms(2) f g fg by (rule functor_comp)
  moreover have "G \<cdot>\<^sub>a (F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f) = G \<cdot>\<^sub>a (F \<cdot>\<^sub>a g) \<circ>\<^bsub>E\<^esub> G \<cdot>\<^sub>a (F \<cdot>\<^sub>a f)"
    using assms(2,3) f g fg by (simp add: functor_comp)
  ultimately show "fcomp C G F \<cdot>\<^sub>a (g \<circ>\<^bsub>C\<^esub> f) = fcomp C G F \<cdot>\<^sub>a g \<circ>\<^bsub>E\<^esub> fcomp C G F \<cdot>\<^sub>a f"
    using assms(1) f g fg by simp
qed (use assms in simp_all)

lemma fcomp_strict:
  assumes "category C" and "is_functor F C D" and "is_functor G D E"
  shows "strict_functor (fcomp C G F) C E"
  using fcomp_functor[OF assms] fcomp_canonical by (rule strict_functorI)

lemma fcomp_assoc:
  assumes "is_functor F C D"
  shows "fcomp C H (fcomp C G F) = fcomp C (fcomp D H G) F"
  unfolding fcomp_def[of C H] fcomp_def[of C "fcomp D H G"]
  using assms by simp

lemma fcomp_idf_left:
  assumes "strict_functor F C D"
  shows "fcomp C (idf D) F = F"
proof -
  have "is_functor F C D"
    using assms by (rule strict_functor_functor)
  then have "fcomp C (idf D) F = mkfun (\<lambda>x\<in>Ob C. F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. F \<cdot>\<^sub>a f)"
    unfolding fcomp_def by simp
  also have "\<dots> = F"
    using assms by (rule strict_functor_canonical[symmetric])
  finally show ?thesis .
qed

lemma fcomp_idf_right:
  assumes "strict_functor F C D"
  shows "fcomp C F (idf C) = F"
proof -
  have "fcomp C F (idf C) = mkfun (\<lambda>x\<in>Ob C. F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. F \<cdot>\<^sub>a f)"
    unfolding fcomp_def by simp
  also have "\<dots> = F"
    using assms by (rule strict_functor_canonical[symmetric])
  finally show ?thesis .
qed

subsection \<open>Functors that agree\<close>

text \<open>
  \<open>agree C\<close> is an equivalence relation on classes. Agreement is all that matters for being a
  functor out of a category and for being a natural transformation, and composition respects it:
  the inner functors must agree on \<open>C\<close>, the outer ones only on the category the inner one lands
  in. Two canonical functors out of \<open>C\<close> that agree are equal.
\<close>

lemma agreeI:
  "(\<And>x. x \<in> Ob C \<Longrightarrow> F \<cdot>\<^sub>o x = G \<cdot>\<^sub>o x) \<Longrightarrow> (\<And>f. f \<in> Arr C \<Longrightarrow> F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f) \<Longrightarrow> agree C F G"
  unfolding agree_def by blast

lemma agree_obj: "agree C F G \<Longrightarrow> x \<in> Ob C \<Longrightarrow> F \<cdot>\<^sub>o x = G \<cdot>\<^sub>o x"
  unfolding agree_def using mem_M by blast

lemma agree_arr: "agree C F G \<Longrightarrow> f \<in> Arr C \<Longrightarrow> F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f"
  unfolding agree_def using mem_M by blast

lemma agree_refl [simp]: "agree C F F"
  by (rule agreeI) simp_all

lemma agree_sym:
  assumes "agree C F G"
  shows "agree C G F"
  by (rule agreeI) (simp_all add: agree_obj[OF assms] agree_arr[OF assms])

lemma agree_trans:
  assumes "agree C F G" and "agree C G H"
  shows "agree C F H"
  by (rule agreeI) (simp_all add: agree_obj[OF assms(1)] agree_arr[OF assms(1)]
      agree_obj[OF assms(2)] agree_arr[OF assms(2)])

lemma strict_functor_eqI:
  assumes "strict_functor F C D" and "strict_functor G C E" and "agree C F G"
  shows "F = G"
proof -
  have "F = mkfun (\<lambda>x\<in>Ob C. F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. F \<cdot>\<^sub>a f)"
    using assms(1) by (rule strict_functor_canonical)
  also have "\<dots> = mkfun (\<lambda>x\<in>Ob C. G \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. G \<cdot>\<^sub>a f)"
    by (simp add: agree_obj[OF assms(3)] agree_arr[OF assms(3)])
  also have "\<dots> = G"
    using assms(2) by (rule strict_functor_canonical[symmetric])
  finally show ?thesis .
qed

lemma functor_agree:
  assumes "category C" and "is_functor F C D" and "agree C F G"
  shows "is_functor G C D"
proof -
  have o: "G \<cdot>\<^sub>o x = F \<cdot>\<^sub>o x" if "x \<in> Ob C" for x
    using agree_obj[OF assms(3) that] by simp
  have a: "G \<cdot>\<^sub>a f = F \<cdot>\<^sub>a f" if "f \<in> Arr C" for f
    using agree_arr[OF assms(3) that] by simp
  show ?thesis
    by (rule is_functorI) (use assms in \<open>simp_all add: o a functor_comp\<close>)
qed

text \<open>Natural transformations, read through rules as categories and functors are.\<close>

lemma nat_transI:
  assumes "\<And>x. x \<in> Ob C \<Longrightarrow> \<theta> \<cdot> x \<in> Arr D"
    and "\<And>x. x \<in> Ob C \<Longrightarrow> src\<^bsub>D\<^esub> (\<theta> \<cdot> x) = F \<cdot>\<^sub>o x"
    and "\<And>x. x \<in> Ob C \<Longrightarrow> tgt\<^bsub>D\<^esub> (\<theta> \<cdot> x) = G \<cdot>\<^sub>o x"
    and "\<And>f. f \<in> Arr C \<Longrightarrow> \<theta> \<cdot> tgt\<^bsub>C\<^esub> f \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f \<circ>\<^bsub>D\<^esub> \<theta> \<cdot> src\<^bsub>C\<^esub> f"
  shows "nat_trans \<theta> F G C D"
  unfolding nat_trans_def using assms by simp

lemma nat_trans_arr [simp]: "nat_trans \<theta> F G C D \<Longrightarrow> x \<in> Ob C \<Longrightarrow> \<theta> \<cdot> x \<in> Arr D"
  unfolding nat_trans_def by (simp add: mem_M)

lemma nat_trans_src [simp]: "nat_trans \<theta> F G C D \<Longrightarrow> x \<in> Ob C \<Longrightarrow> src\<^bsub>D\<^esub> (\<theta> \<cdot> x) = F \<cdot>\<^sub>o x"
  unfolding nat_trans_def by (simp add: mem_M)

lemma nat_trans_tgt [simp]: "nat_trans \<theta> F G C D \<Longrightarrow> x \<in> Ob C \<Longrightarrow> tgt\<^bsub>D\<^esub> (\<theta> \<cdot> x) = G \<cdot>\<^sub>o x"
  unfolding nat_trans_def by (simp add: mem_M)

lemma nat_trans_nat:
  "nat_trans \<theta> F G C D \<Longrightarrow> f \<in> Arr C \<Longrightarrow> \<theta> \<cdot> tgt\<^bsub>C\<^esub> f \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f \<circ>\<^bsub>D\<^esub> \<theta> \<cdot> src\<^bsub>C\<^esub> f"
  unfolding nat_trans_def by (simp add: mem_M)

lemma nat_trans_agree:
  assumes "nat_trans \<theta> F G C D" and "agree C F F'" and "agree C G G'"
  shows "nat_trans \<theta> F' G' C D"
proof -
  have o: "F' \<cdot>\<^sub>o x = F \<cdot>\<^sub>o x" "G' \<cdot>\<^sub>o x = G \<cdot>\<^sub>o x" if "x \<in> Ob C" for x
    using agree_obj[OF assms(2) that] agree_obj[OF assms(3) that] by simp_all
  have a: "F' \<cdot>\<^sub>a f = F \<cdot>\<^sub>a f" "G' \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f" if "f \<in> Arr C" for f
    using agree_arr[OF assms(2) that] agree_arr[OF assms(3) that] by simp_all
  show ?thesis
    by (rule nat_transI) (use assms(1) in \<open>simp_all add: o a nat_trans_nat\<close>)
qed

lemma fcomp_agree_inner:
  assumes "agree C F F'"
  shows "agree C (fcomp C G F) (fcomp C G F')"
  by (rule agreeI) (simp_all add: agree_obj[OF assms] agree_arr[OF assms])

lemma fcomp_agree_outer:
  assumes "is_functor F C D" and "agree D G G'"
  shows "agree C (fcomp C G F) (fcomp C G' F)"
  by (rule agreeI) (use assms(1) in \<open>simp_all add: agree_obj[OF assms(2)] agree_arr[OF assms(2)]\<close>)

lemma fcomp_agree:
  assumes "agree C F F'" and "is_functor F C D" and "agree D G G'"
  shows "agree C (fcomp C G F) (fcomp C G' F')"
  using fcomp_agree_outer[OF assms(2,3)] fcomp_agree_inner[OF assms(1)] by (rule agree_trans)

end
