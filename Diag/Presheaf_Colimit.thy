section \<open>The presheaf of a diagram is the colimit of its representables\<close>

theory Presheaf_Colimit
  imports Adequacy Yoneda_Check
begin

text \<open>
  \<open>Adequacy\<close> shows that the arrows of \<open>PSh C\<close> are the natural transformations between the
  presheaves \<open>elts C X\<close>. This theory states the other half of the comparison with the small
  presheaves of the note: \<open>elts C X\<close>, for \<open>X = \<langle>J, F\<rangle>\<close>, is the colimit of the representables
  \<open>y(F j)\<close> in the presheaves on \<open>C\<close>; a presheaf that is such a colimit is isomorphic to it; and
  \<open>colim_functor C\<close> is the map of colimits induced by a morphism of diagrams. The last part
  carries the comparison from the presheaves \<open>elts C X\<close> to arbitrary small presheaves. Nothing
  here is used by the localization theorem.

  A presheaf on \<open>C\<close> is given by two classes: \<open>Q\<close>, with the set \<open>Q \<cdot> c\<close> at an object \<open>c\<close> (an
  application is always a set), and \<open>R\<close>, with \<open>R \<cdot> \<langle>u, x\<rangle>\<close> the restriction of \<open>x \<in> Q \<cdot> tgt u\<close>
  along \<open>u\<close>. Every functor from the opposite of \<open>C\<close> to sets that is a class is of this form. A
  map of presheaves is a class \<open>\<eta>\<close> with component \<open>\<eta> \<cdot> \<langle>c, x\<rangle>\<close>, as in \<open>Adequacy\<close>. A cocone under
  \<open>y \<circ> F\<close> with vertex \<open>(Q, R)\<close> is a class \<open>l\<close>: the leg at \<open>j\<close> is the natural transformation
  \<open>Hom(-, F j) \<rightarrow> Q\<close> sending \<open>f : c \<rightarrow> F j\<close> to \<open>l \<cdot> \<langle>j, f\<rangle>\<close>, and the legs are compatible with the
  arrows of \<open>J\<close>. The predicates below quantify over such classes, so "colimit" means colimit
  among all presheaves on \<open>C\<close> that are classes.
\<close>

subsection \<open>Presheaves, their maps, and cocones of representables\<close>

definition presheaf :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "presheaf C Q R \<longleftrightarrow>
    (\<forall>\<^sub>s u x. u \<in> Arr C \<longrightarrow> x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u \<longrightarrow> R \<cdot> \<langle>u, x\<rangle> \<in> Q \<cdot> src\<^bsub>C\<^esub> u) \<and>
    (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> Q \<cdot> c \<longrightarrow> R \<cdot> \<langle>id\<^bsub>C\<^esub> c, x\<rangle> = x) \<and>
    (\<forall>\<^sub>s u v x. u \<in> Arr C \<longrightarrow> v \<in> Arr C \<longrightarrow> src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u \<longrightarrow> x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> v \<longrightarrow>
      R \<cdot> \<langle>v \<circ>\<^bsub>C\<^esub> u, x\<rangle> = R \<cdot> \<langle>u, R \<cdot> \<langle>v, x\<rangle>\<rangle>)"

definition psh_map :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "psh_map C Q R Q' R' \<eta> \<longleftrightarrow>
    (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> Q \<cdot> c \<longrightarrow> \<eta> \<cdot> \<langle>c, x\<rangle> \<in> Q' \<cdot> c) \<and>
    (\<forall>\<^sub>s u x. u \<in> Arr C \<longrightarrow> x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u \<longrightarrow>
      \<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, x\<rangle>\<rangle> = R' \<cdot> \<langle>u, \<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>)"

text \<open>Two maps out of \<open>Q\<close> with the same components.\<close>

definition psh_agree :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "psh_agree C Q \<eta> \<eta>' \<longleftrightarrow>
    (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> Q \<cdot> c \<longrightarrow> \<eta> \<cdot> \<langle>c, x\<rangle> = \<eta>' \<cdot> \<langle>c, x\<rangle>)"

definition psh_iso :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "psh_iso C Q R Q' R' \<longleftrightarrow>
    (\<exists>\<mu> \<nu>. psh_map C Q R Q' R' \<mu> \<and> psh_map C Q' R' Q R \<nu> \<and>
      (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> Q \<cdot> c \<longrightarrow> \<nu> \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x) \<and>
      (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> Q' \<cdot> c \<longrightarrow> \<mu> \<cdot> \<langle>c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x))"

text \<open>
  \<open>cocone C X Q R l\<close>, for \<open>X = \<langle>J, F\<rangle>\<close>: the values lie in \<open>Q\<close>; each leg is natural, that is
  \<open>l \<cdot> \<langle>j, f \<circ> u\<rangle>\<close> is the restriction of \<open>l \<cdot> \<langle>j, f\<rangle>\<close> along \<open>u\<close>; and the leg at \<open>tgt b\<close> composed
  with \<open>y(F b)\<close> is the leg at \<open>src b\<close>, for every arrow \<open>b\<close> of \<open>J\<close>.
\<close>

definition cocone :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "cocone C X Q R l \<longleftrightarrow>
    (\<forall>\<^sub>s c j f. c \<in> Ob C \<longrightarrow> j \<in> Ob (ix X) \<longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<longrightarrow> l \<cdot> \<langle>j, f\<rangle> \<in> Q \<cdot> c) \<and>
    (\<forall>\<^sub>s u j f. u \<in> Arr C \<longrightarrow> j \<in> Ob (ix X) \<longrightarrow> f \<in> Hom C (tgt\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j) \<longrightarrow>
      l \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle> = R \<cdot> \<langle>u, l \<cdot> \<langle>j, f\<rangle>\<rangle>) \<and>
    (\<forall>\<^sub>s c b f. c \<in> Ob C \<longrightarrow> b \<in> Arr (ix X) \<longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b) \<longrightarrow>
      l \<cdot> \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle> = l \<cdot> \<langle>src\<^bsub>ix X\<^esub> b, f\<rangle>)"

text \<open>\<open>mediates C X l l' \<mu>\<close>: the map \<open>\<mu>\<close> carries the cocone \<open>l\<close> to the cocone \<open>l'\<close>.\<close>

definition mediates :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "mediates C X l l' \<mu> \<longleftrightarrow>
    (\<forall>\<^sub>s c j f. c \<in> Ob C \<longrightarrow> j \<in> Ob (ix X) \<longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<longrightarrow>
      \<mu> \<cdot> \<langle>c, l \<cdot> \<langle>j, f\<rangle>\<rangle> = l' \<cdot> \<langle>j, f\<rangle>)"

text \<open>
  \<open>colimiting C X Q R l\<close>: the cocone \<open>l\<close> with vertex \<open>(Q, R)\<close> is a colimit of \<open>y \<circ> F\<close>. Every
  cocone under \<open>y \<circ> F\<close> is the image of \<open>l\<close> under a map of presheaves, and two such maps have the
  same components.
\<close>

definition colimiting :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "colimiting C X Q R l \<longleftrightarrow>
    presheaf C Q R \<and> cocone C X Q R l \<and>
    (\<forall>Q' R' l'. presheaf C Q' R' \<longrightarrow> cocone C X Q' R' l' \<longrightarrow>
      (\<exists>\<mu>. psh_map C Q R Q' R' \<mu> \<and> mediates C X l l' \<mu>) \<and>
      (\<forall>\<mu> \<mu>'. psh_map C Q R Q' R' \<mu> \<longrightarrow> mediates C X l l' \<mu> \<longrightarrow>
        psh_map C Q R Q' R' \<mu>' \<longrightarrow> mediates C X l l' \<mu>' \<longrightarrow> psh_agree C Q \<mu> \<mu>'))"

text \<open>
  Definition 1.1 of the note: a presheaf is small if it is the colimit, among all presheaves, of
  \<open>y \<circ> F\<close> for some small diagram \<open>\<langle>J, F\<rangle>\<close>.
\<close>

definition small_presheaf :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "small_presheaf C Q R \<longleftrightarrow> (\<exists>X l. X \<in> DOb C \<and> colimiting C X Q R l)"

subsection \<open>The presheaf of a diagram, as classes\<close>

text \<open>
  The pairs on which the class functions below are defined: \<open>\<langle>c, \<kappa>\<rangle>\<close> with \<open>\<kappa>\<close> an element at \<open>c\<close>;
  \<open>\<langle>u, \<kappa>\<rangle>\<close> with \<open>\<kappa>\<close> an element at the target of \<open>u\<close>; and \<open>\<langle>j, f\<rangle>\<close> with \<open>f\<close> an arrow of \<open>C\<close> into
  \<open>F j\<close>.
\<close>

definition elts_pairs :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "elts_pairs C X = \<lbrace>p. \<exists>\<^sub>s c \<kappa>. p = \<langle>c, \<kappa>\<rangle> \<and> c \<in> Ob C \<and> \<kappa> \<in> elts C X c\<rbrace>"

definition pre_pairs :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "pre_pairs C X = \<lbrace>p. \<exists>\<^sub>s u \<kappa>. p = \<langle>u, \<kappa>\<rangle> \<and> u \<in> Arr C \<and> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u)\<rbrace>"

definition leg_pairs :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "leg_pairs C X =
    \<lbrace>v. \<exists>\<^sub>s j f. v = \<langle>j, f\<rangle> \<and> j \<in> Ob (ix X) \<and> f \<in> Arr C \<and> tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j\<rbrace>"

text \<open>
  \<open>elts_fun C X\<close> and \<open>pre_fun C X\<close>: the presheaf \<open>c \<mapsto> elts C X c\<close> with restriction \<open>pre C X\<close>.
  \<open>inj_fun C X\<close>: its cocone, sending \<open>f : c \<rightarrow> F j\<close> to the component of \<open>\<langle>j, f\<rangle>\<close> in \<open>(c \<down> F)\<close>.
  \<open>act_fun C \<phi>\<close>: the map \<open>act C \<phi>\<close> of an arrow \<open>\<phi>\<close> of \<open>PSh C\<close>.
\<close>

definition elts_fun :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "elts_fun C X = (\<lambda>c\<in>Ob C. elts C X c)"

definition pre_fun :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "pre_fun C X = (\<lambda>p\<in>pre_pairs C X. pre C X (pfst p) (psnd p))"

definition inj_fun :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "inj_fun C X = (\<lambda>v\<in>leg_pairs C X. cc (cgraph C X (src\<^bsub>C\<^esub> (psnd v))) v)"

definition act_fun :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "act_fun C \<phi> = (\<lambda>p\<in>elts_pairs C (asrc \<phi>). act C \<phi> (pfst p) (psnd p))"

text \<open>
  \<open>push C a\<close>, for a morphism \<open>a = (p, \<alpha>) : \<langle>J, F\<rangle> \<rightarrow> \<langle>K, G\<rangle>\<close> of diagrams: the cocone under
  \<open>y \<circ> F\<close> with vertex the presheaf of \<open>\<langle>K, G\<rangle>\<close> whose leg at \<open>j\<close> is \<open>y(\<alpha>\<^sub>j)\<close> followed by the leg
  at \<open>p j\<close>. The map it induces is the composite \<open>colim y F \<rightarrow> colim y G p \<rightarrow> colim y G\<close> of
  Definition 3.1.
\<close>

definition push :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "push C a =
    (\<lambda>v\<in>leg_pairs C (asrc a).
      inj_fun C (atgt a) \<cdot> \<langle>afun a \<cdot>\<^sub>o pfst v, (anat a \<cdot> pfst v) \<circ>\<^bsub>C\<^esub> psnd v\<rangle>)"

subsection \<open>Class existence and the classes of pairs\<close>

lemma dcls_elts_pairs [dfn_rules]: "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dcls (\<lambda>x. elts_pairs (C x) (X x))"
  unfolding elts_pairs_def by dfn

lemma dcls_pre_pairs [dfn_rules]: "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dcls (\<lambda>x. pre_pairs (C x) (X x))"
  unfolding pre_pairs_def by dfn

lemma dcls_leg_pairs [dfn_rules]: "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dcls (\<lambda>x. leg_pairs (C x) (X x))"
  unfolding leg_pairs_def by dfn

lemma dcls_inj_fun [dfn_rules]: "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dcls (\<lambda>x. inj_fun (C x) (X x))"
  unfolding inj_fun_def by dfn

lemma mem_elts_pairs:
  "p \<in> elts_pairs C X \<longleftrightarrow> M p \<and> (\<exists>\<^sub>s c \<kappa>. p = \<langle>c, \<kappa>\<rangle> \<and> c \<in> Ob C \<and> \<kappa> \<in> elts C X c)"
  unfolding elts_pairs_def by simp

lemma mem_pre_pairs:
  "p \<in> pre_pairs C X \<longleftrightarrow> M p \<and> (\<exists>\<^sub>s u \<kappa>. p = \<langle>u, \<kappa>\<rangle> \<and> u \<in> Arr C \<and> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u))"
  unfolding pre_pairs_def by simp

lemma mem_leg_pairs:
  "v \<in> leg_pairs C X \<longleftrightarrow>
    M v \<and> (\<exists>\<^sub>s j f. v = \<langle>j, f\<rangle> \<and> j \<in> Ob (ix X) \<and> f \<in> Arr C \<and> tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j)"
  unfolding leg_pairs_def by simp

lemma elts_pairsI:
  assumes "c \<in> Ob C" and "\<kappa> \<in> elts C X c"
  shows "\<langle>c, \<kappa>\<rangle> \<in> elts_pairs C X"
  unfolding mem_elts_pairs using assms mem_M[OF assms(1)] mem_M[OF assms(2)] M_opair by blast

lemma pre_pairsI:
  assumes "u \<in> Arr C" and "\<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
  shows "\<langle>u, \<kappa>\<rangle> \<in> pre_pairs C X"
  unfolding mem_pre_pairs using assms mem_M[OF assms(1)] mem_M[OF assms(2)] M_opair by blast

lemma leg_pairsI:
  assumes "j \<in> Ob (ix X)" and "f \<in> Arr C" and "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
  shows "\<langle>j, f\<rangle> \<in> leg_pairs C X"
  unfolding mem_leg_pairs using assms mem_M[OF assms(1)] mem_M[OF assms(2)] M_opair by blast

subsection \<open>Beta rules\<close>

text \<open>
  The values of the four class functions on the pairs they are meant for. Each is \<open>app_Lam\<close>,
  with the value shown to be a set.
\<close>

context
  fixes C X
  assumes C: "category C" and ls: "locally_small C" and X: "X \<in> DOb C"
begin

lemma elts_fun_app:
  assumes c: "c \<in> Ob C"
  shows "elts_fun C X \<cdot> c = elts C X c"
proof -
  have d: "dcls (\<lambda>c. elts C X c)"
    by dfn
  show ?thesis
    unfolding elts_fun_def by (rule app_Lam[OF d c M_elts[OF C ls X c]])
qed

lemma pre_fun_app:
  assumes u: "u \<in> Arr C" and \<kappa>: "\<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
  shows "pre_fun C X \<cdot> \<langle>u, \<kappa>\<rangle> = pre C X u \<kappa>"
proof -
  have "M u" and "M \<kappa>"
    using u \<kappa> by (simp_all add: mem_M)
  have d: "dcls (\<lambda>p. pre C X (pfst p) (psnd p))"
    by dfn
  have "M (pre C X (pfst \<langle>u, \<kappa>\<rangle>) (psnd \<langle>u, \<kappa>\<rangle>))"
    using mem_M[OF pre_elts[OF C ls X u \<kappa>]] \<open>M u\<close> \<open>M \<kappa>\<close> by simp
  then have "pre_fun C X \<cdot> \<langle>u, \<kappa>\<rangle> = pre C X (pfst \<langle>u, \<kappa>\<rangle>) (psnd \<langle>u, \<kappa>\<rangle>)"
    unfolding pre_fun_def by (rule app_Lam[OF d pre_pairsI[OF u \<kappa>]])
  then show ?thesis
    using \<open>M u\<close> \<open>M \<kappa>\<close> by simp
qed

lemma inj_fun_app:
  assumes c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
  shows "inj_fun C X \<cdot> \<langle>j, f\<rangle> = cc (cgraph C X c) \<langle>j, f\<rangle>"
proof -
  have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
    using f by simp_all
  have "M j" and "M f"
    using j fa(1) by (simp_all add: mem_M)
  have d: "dcls (\<lambda>v. cc (cgraph C X (src\<^bsub>C\<^esub> (psnd v))) v)"
    by dfn
  have "M (cc (cgraph C X (src\<^bsub>C\<^esub> (psnd \<langle>j, f\<rangle>))) \<langle>j, f\<rangle>)"
    using C ls X c fa \<open>M j\<close> \<open>M f\<close> by simp
  then have "inj_fun C X \<cdot> \<langle>j, f\<rangle> = cc (cgraph C X (src\<^bsub>C\<^esub> (psnd \<langle>j, f\<rangle>))) \<langle>j, f\<rangle>"
    unfolding inj_fun_def by (rule app_Lam[OF d leg_pairsI[OF j fa(1) fa(3)]])
  then show ?thesis
    using fa \<open>M j\<close> \<open>M f\<close> by simp
qed

end

lemma act_fun_app:
  assumes C: "category C" and ls: "locally_small C" and \<phi>: "\<phi> \<in> PArr C"
    and c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C (asrc \<phi>) c"
  shows "act_fun C \<phi> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>"
proof -
  have "M c" and "M \<kappa>"
    using c \<kappa> by (simp_all add: mem_M)
  have d: "dcls (\<lambda>p. act C \<phi> (pfst p) (psnd p))"
    by dfn
  have "M (act C \<phi> (pfst \<langle>c, \<kappa>\<rangle>) (psnd \<langle>c, \<kappa>\<rangle>))"
    using mem_M[OF act_elts[OF C ls \<phi> \<kappa>]] \<open>M c\<close> \<open>M \<kappa>\<close> by simp
  then have "act_fun C \<phi> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> (pfst \<langle>c, \<kappa>\<rangle>) (psnd \<langle>c, \<kappa>\<rangle>)"
    unfolding act_fun_def by (rule app_Lam[OF d elts_pairsI[OF c \<kappa>]])
  then show ?thesis
    using \<open>M c\<close> \<open>M \<kappa>\<close> by simp
qed

lemma push_app:
  assumes a: "a \<in> DArr C" and j: "j \<in> Ob (ix (asrc a))"
    and f: "f \<in> Arr C" "tgt\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j"
  shows "push C a \<cdot> \<langle>j, f\<rangle> = inj_fun C (atgt a) \<cdot> \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  have "M j" and "M f"
    using j f(1) by (simp_all add: mem_M)
  have d: "dcls (\<lambda>v. inj_fun C (atgt a) \<cdot> \<langle>afun a \<cdot>\<^sub>o pfst v, (anat a \<cdot> pfst v) \<circ>\<^bsub>C\<^esub> psnd v\<rangle>)"
    by dfn
  have "push C a \<cdot> \<langle>j, f\<rangle> =
      inj_fun C (atgt a) \<cdot> \<langle>afun a \<cdot>\<^sub>o pfst \<langle>j, f\<rangle>, (anat a \<cdot> pfst \<langle>j, f\<rangle>) \<circ>\<^bsub>C\<^esub> psnd \<langle>j, f\<rangle>\<rangle>"
    unfolding push_def by (rule app_Lam[OF d leg_pairsI[OF j f] M_app])
  then show ?thesis
    using \<open>M j\<close> \<open>M f\<close> by simp
qed

lemma push_cc:
  assumes C: "category C" and ls: "locally_small C" and a: "a \<in> DArr C"
    and c: "c \<in> Ob C" and j: "j \<in> Ob (ix (asrc a))" and f: "f \<in> Hom C c (dg (asrc a) \<cdot>\<^sub>o j)"
  shows "push C a \<cdot> \<langle>j, f\<rangle> = cc (cgraph C (atgt a) c) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  have fa: "f \<in> Arr C" "tgt\<^bsub>C\<^esub> f = dg (asrc a) \<cdot>\<^sub>o j"
    using f by simp_all
  have pj: "afun a \<cdot>\<^sub>o j \<in> Ob (ix (atgt a))"
    using DArr_functor[OF a] j by simp
  have \<alpha>f: "anat a \<cdot> j \<circ>\<^bsub>C\<^esub> f \<in> Hom C c (dg (atgt a) \<cdot>\<^sub>o (afun a \<cdot>\<^sub>o j))"
    using C a j f by simp
  show ?thesis
    unfolding push_app[OF a j fa] by (rule inj_fun_app[OF C ls DArr_atgt[OF a] c pj \<alpha>f])
qed

subsection \<open>Reading the predicates\<close>

text \<open>Introduction and destruction rules for the predicates of this theory, without \<open>\<forall>\<^sub>s\<close>.\<close>

lemma psh_mapI:
  assumes "\<And>c x. c \<in> Ob C \<Longrightarrow> x \<in> Q \<cdot> c \<Longrightarrow> \<eta> \<cdot> \<langle>c, x\<rangle> \<in> Q' \<cdot> c"
    and "\<And>u x. u \<in> Arr C \<Longrightarrow> x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u \<Longrightarrow>
      \<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, x\<rangle>\<rangle> = R' \<cdot> \<langle>u, \<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>"
  shows "psh_map C Q R Q' R' \<eta>"
  unfolding psh_map_def using assms by blast

lemma psh_map_val:
  assumes "psh_map C Q R Q' R' \<eta>" and "c \<in> Ob C" and "x \<in> Q \<cdot> c"
  shows "\<eta> \<cdot> \<langle>c, x\<rangle> \<in> Q' \<cdot> c"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding psh_map_def by blast

lemma psh_map_nat:
  assumes "psh_map C Q R Q' R' \<eta>" and "u \<in> Arr C" and "x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u"
  shows "\<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, x\<rangle>\<rangle> = R' \<cdot> \<langle>u, \<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding psh_map_def by blast

lemma psh_agreeI:
  assumes "\<And>c x. c \<in> Ob C \<Longrightarrow> x \<in> Q \<cdot> c \<Longrightarrow> \<eta> \<cdot> \<langle>c, x\<rangle> = \<eta>' \<cdot> \<langle>c, x\<rangle>"
  shows "psh_agree C Q \<eta> \<eta>'"
  unfolding psh_agree_def using assms by blast

lemma psh_agreeD:
  assumes "psh_agree C Q \<eta> \<eta>'" and "c \<in> Ob C" and "x \<in> Q \<cdot> c"
  shows "\<eta> \<cdot> \<langle>c, x\<rangle> = \<eta>' \<cdot> \<langle>c, x\<rangle>"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding psh_agree_def by blast

lemma coconeI:
  assumes "\<And>c j f. c \<in> Ob C \<Longrightarrow> j \<in> Ob (ix X) \<Longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<Longrightarrow> l \<cdot> \<langle>j, f\<rangle> \<in> Q \<cdot> c"
    and "\<And>u j f. u \<in> Arr C \<Longrightarrow> j \<in> Ob (ix X) \<Longrightarrow> f \<in> Hom C (tgt\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j) \<Longrightarrow>
      l \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle> = R \<cdot> \<langle>u, l \<cdot> \<langle>j, f\<rangle>\<rangle>"
    and "\<And>c b f. c \<in> Ob C \<Longrightarrow> b \<in> Arr (ix X) \<Longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b) \<Longrightarrow>
      l \<cdot> \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle> = l \<cdot> \<langle>src\<^bsub>ix X\<^esub> b, f\<rangle>"
  shows "cocone C X Q R l"
  unfolding cocone_def using assms by blast

lemma cocone_val:
  assumes "cocone C X Q R l" and "c \<in> Ob C" and "j \<in> Ob (ix X)" and "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
  shows "l \<cdot> \<langle>j, f\<rangle> \<in> Q \<cdot> c"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] mem_M[OF assms(4)]
  unfolding cocone_def by blast

lemma cocone_nat:
  assumes "cocone C X Q R l" and "u \<in> Arr C" and "j \<in> Ob (ix X)"
    and "f \<in> Hom C (tgt\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j)"
  shows "l \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle> = R \<cdot> \<langle>u, l \<cdot> \<langle>j, f\<rangle>\<rangle>"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] mem_M[OF assms(4)]
  unfolding cocone_def by blast

lemma cocone_compat:
  assumes "cocone C X Q R l" and "c \<in> Ob C" and "b \<in> Arr (ix X)"
    and "f \<in> Hom C c (dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b)"
  shows "l \<cdot> \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle> = l \<cdot> \<langle>src\<^bsub>ix X\<^esub> b, f\<rangle>"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] mem_M[OF assms(4)]
  unfolding cocone_def by blast

lemma mediatesI:
  assumes "\<And>c j f. c \<in> Ob C \<Longrightarrow> j \<in> Ob (ix X) \<Longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<Longrightarrow>
    \<mu> \<cdot> \<langle>c, l \<cdot> \<langle>j, f\<rangle>\<rangle> = l' \<cdot> \<langle>j, f\<rangle>"
  shows "mediates C X l l' \<mu>"
  unfolding mediates_def using assms by blast

lemma mediatesD:
  assumes "mediates C X l l' \<mu>" and "c \<in> Ob C" and "j \<in> Ob (ix X)" and "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
  shows "\<mu> \<cdot> \<langle>c, l \<cdot> \<langle>j, f\<rangle>\<rangle> = l' \<cdot> \<langle>j, f\<rangle>"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] mem_M[OF assms(4)]
  unfolding mediates_def by blast

lemma colimitingI:
  assumes "presheaf C Q R" and "cocone C X Q R l"
    and "\<And>Q' R' l'. presheaf C Q' R' \<Longrightarrow> cocone C X Q' R' l' \<Longrightarrow>
      \<exists>\<mu>. psh_map C Q R Q' R' \<mu> \<and> mediates C X l l' \<mu>"
    and "\<And>Q' R' l' \<mu> \<mu>'. presheaf C Q' R' \<Longrightarrow> cocone C X Q' R' l' \<Longrightarrow>
      psh_map C Q R Q' R' \<mu> \<Longrightarrow> mediates C X l l' \<mu> \<Longrightarrow>
      psh_map C Q R Q' R' \<mu>' \<Longrightarrow> mediates C X l l' \<mu>' \<Longrightarrow> psh_agree C Q \<mu> \<mu>'"
  shows "colimiting C X Q R l"
  unfolding colimiting_def using assms by blast

lemma colimiting_presheaf: "colimiting C X Q R l \<Longrightarrow> presheaf C Q R"
  unfolding colimiting_def by blast

lemma colimiting_cocone: "colimiting C X Q R l \<Longrightarrow> cocone C X Q R l"
  unfolding colimiting_def by blast

lemma colimiting_ex:
  assumes "colimiting C X Q R l" and "presheaf C Q' R'" and "cocone C X Q' R' l'"
  shows "\<exists>\<mu>. psh_map C Q R Q' R' \<mu> \<and> mediates C X l l' \<mu>"
  using assms unfolding colimiting_def by blast

lemma colimiting_unique:
  assumes "colimiting C X Q R l" and "presheaf C Q' R'" and "cocone C X Q' R' l'"
    and "psh_map C Q R Q' R' \<mu>" and "mediates C X l l' \<mu>"
    and "psh_map C Q R Q' R' \<mu>'" and "mediates C X l l' \<mu>'"
  shows "psh_agree C Q \<mu> \<mu>'"
  using assms unfolding colimiting_def by blast

subsection \<open>Composite and identity maps of presheaves\<close>

text \<open>
  Maps of presheaves written as classes on all pairs \<open>\<langle>c, x\<rangle>\<close>: the composite of \<open>\<mu>\<close> and \<open>\<nu>\<close>,
  and the identity. Both are maps of presheaves, and composites carry cocones as their factors
  do.
\<close>

lemma app_comp_Lam:
  assumes "M c" and "M x"
  shows "(\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) \<cdot> \<langle>c, x\<rangle> = \<nu> \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, x\<rangle>\<rangle>"
proof -
  have d: "dcls (\<lambda>p. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>)"
    by dfn
  have "(\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) \<cdot> \<langle>c, x\<rangle> = \<nu> \<cdot> \<langle>pfst \<langle>c, x\<rangle>, \<mu> \<cdot> \<langle>c, x\<rangle>\<rangle>"
    by (rule app_Lam[OF d]) simp_all
  then show ?thesis
    using assms by simp
qed

lemma app_id_Lam:
  assumes "M c" and "M x"
  shows "(\<lambda>p\<in>\<V>. psnd p) \<cdot> \<langle>c, x\<rangle> = x"
proof -
  have d: "dcls (\<lambda>p. psnd p)"
    by dfn
  have "(\<lambda>p\<in>\<V>. psnd p) \<cdot> \<langle>c, x\<rangle> = psnd \<langle>c, x\<rangle>"
    by (rule app_Lam[OF d]) (use assms in simp_all)
  then show ?thesis
    using assms by simp
qed

lemma psh_map_comp:
  assumes C: "category C" and \<mu>: "psh_map C Q R Q' R' \<mu>" and \<nu>: "psh_map C Q' R' Q'' R'' \<nu>"
  shows "psh_map C Q R Q'' R'' (\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>)"
proof (rule psh_mapI)
  fix c x
  assume c: "c \<in> Ob C" and x: "x \<in> Q \<cdot> c"
  have "\<nu> \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, x\<rangle>\<rangle> \<in> Q'' \<cdot> c"
    by (rule psh_map_val[OF \<nu> c psh_map_val[OF \<mu> c x]])
  then show "(\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) \<cdot> \<langle>c, x\<rangle> \<in> Q'' \<cdot> c"
    unfolding app_comp_Lam[OF mem_M[OF c] mem_M[OF x]] .
next
  fix u x
  assume u: "u \<in> Arr C" and x: "x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u"
  have tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C"
    using C u by simp
  have "\<nu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, x\<rangle>\<rangle>\<rangle> = \<nu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R' \<cdot> \<langle>u, \<mu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>\<rangle>"
    unfolding psh_map_nat[OF \<mu> u x] by (rule refl)
  also have "\<dots> = R'' \<cdot> \<langle>u, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, \<mu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>\<rangle>"
    by (rule psh_map_nat[OF \<nu> u psh_map_val[OF \<mu> tu x]])
  finally show "(\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, x\<rangle>\<rangle> =
      R'' \<cdot> \<langle>u, (\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>"
    unfolding app_comp_Lam[OF M_src M_app] app_comp_Lam[OF M_tgt mem_M[OF x]] .
qed

lemma mediates_comp:
  assumes \<mu>: "mediates C X l l' \<mu>" and \<nu>: "mediates C X l' l'' \<nu>"
  shows "mediates C X l l'' (\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>)"
proof (rule mediatesI)
  fix c j f
  assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
  show "(\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) \<cdot> \<langle>c, l \<cdot> \<langle>j, f\<rangle>\<rangle> = l'' \<cdot> \<langle>j, f\<rangle>"
    unfolding app_comp_Lam[OF mem_M[OF c] M_app] mediatesD[OF \<mu> c j f] mediatesD[OF \<nu> c j f]
    by (rule refl)
qed

lemma psh_map_id: "psh_map C Q R Q R (\<lambda>p\<in>\<V>. psnd p)"
proof (rule psh_mapI)
  fix c x
  assume c: "c \<in> Ob C" and x: "x \<in> Q \<cdot> c"
  show "(\<lambda>p\<in>\<V>. psnd p) \<cdot> \<langle>c, x\<rangle> \<in> Q \<cdot> c"
    unfolding app_id_Lam[OF mem_M[OF c] mem_M[OF x]] by (rule x)
next
  fix u x
  assume u: "u \<in> Arr C" and x: "x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u"
  show "(\<lambda>p\<in>\<V>. psnd p) \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, x\<rangle>\<rangle> = R \<cdot> \<langle>u, (\<lambda>p\<in>\<V>. psnd p) \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>"
    unfolding app_id_Lam[OF M_src M_app] app_id_Lam[OF M_tgt mem_M[OF x]] by (rule refl)
qed

lemma mediates_id: "mediates C X l l (\<lambda>p\<in>\<V>. psnd p)"
proof (rule mediatesI)
  fix c j f
  assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
  show "(\<lambda>p\<in>\<V>. psnd p) \<cdot> \<langle>c, l \<cdot> \<langle>j, f\<rangle>\<rangle> = l \<cdot> \<langle>j, f\<rangle>"
    by (rule app_id_Lam[OF mem_M[OF c] M_app])
qed

subsection \<open>A cocone is constant on components\<close>

text \<open>
  Along an edge \<open>\<langle>s b, h\<rangle> \<rightarrow> \<langle>t b, F b \<circ> h\<rangle>\<close> of \<open>(c \<down> F)\<close> a cocone takes the same value, by its third
  clause; so it takes the same value on connected vertices. Hence the class of the pairs
  \<open>\<langle>\<langle>c, \<kappa>\<rangle>, l \<cdot> v\<rangle>\<close> with \<open>v \<in> \<kappa>\<close> is single-valued, and it is the mediating map.
\<close>

lemma cocone_conn:
  assumes cone: "cocone C X Q R l" and X: "X \<in> DOb C" and C: "category C"
    and ls: "locally_small C" and c: "c \<in> Ob C" and "M u" and cw: "conn (cgraph C X c) u w"
  shows "l \<cdot> w = l \<cdot> u"
proof -
  define P where "P = (\<lambda>w. l \<cdot> w = l \<cdot> u)"
  have dP: "dfn P"
    unfolding P_def by dfn
  have Pu: "P u"
    unfolding P_def by simp
  have step: "P a \<longleftrightarrow> P b"
    if ab: "M a" "M b" "\<langle>a, b\<rangle> \<in> cgraph C X c" "conn (cgraph C X c) u a" for a b
  proof -
    obtain h e where a: "a = \<langle>src\<^bsub>ix X\<^esub> e, h\<rangle>" and b: "b = \<langle>tgt\<^bsub>ix X\<^esub> e, dg X \<cdot>\<^sub>a e \<circ>\<^bsub>C\<^esub> h\<rangle>"
      and e: "e \<in> Arr (ix X)" and h: "h \<in> Arr C" "src\<^bsub>C\<^esub> h = c" "tgt\<^bsub>C\<^esub> h = dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> e"
      using ab(3,1,2) by (rule comma_edge_pairE)
    have hH: "h \<in> Hom C c (dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> e)"
      using h by simp
    have "l \<cdot> b = l \<cdot> a"
      unfolding a b by (rule cocone_compat[OF cone c e hH])
    then show ?thesis
      unfolding P_def by simp
  qed
  have "P w"
    by (rule conn_induct[OF M_cgraph[OF C ls X c] \<open>M u\<close> cw dP Pu step])
  then show ?thesis
    unfolding P_def .
qed

lemma med_app:
  assumes C: "category C" and ls: "locally_small C" and X: "X \<in> DOb C"
    and cone: "cocone C X Q R l"
    and c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C X c" and jf: "\<langle>j, f\<rangle> \<in> \<kappa>" and "M j" and "M f"
  shows "\<lbrace>p. \<exists>\<^sub>s c \<kappa> j f. p = \<langle>\<langle>c, \<kappa>\<rangle>, l \<cdot> \<langle>j, f\<rangle>\<rangle> \<and> c \<in> Ob C \<and> \<kappa> \<in> elts C X c \<and> \<langle>j, f\<rangle> \<in> \<kappa>\<rbrace> \<cdot> \<langle>c, \<kappa>\<rangle> =
    l \<cdot> \<langle>j, f\<rangle>"
proof -
  let ?P = "\<lambda>p. \<exists>\<^sub>s c \<kappa> j f. p = \<langle>\<langle>c, \<kappa>\<rangle>, l \<cdot> \<langle>j, f\<rangle>\<rangle> \<and> c \<in> Ob C \<and> \<kappa> \<in> elts C X c \<and> \<langle>j, f\<rangle> \<in> \<kappa>"
  have dP: "dfn ?P"
    by dfn
  note mem = Coll_iff[OF dP]
  have "M c" and "M \<kappa>"
    using c \<kappa> by (simp_all add: mem_M)
  show ?thesis
  proof (rule app_eq)
    show "M (l \<cdot> \<langle>j, f\<rangle>)"
      by simp
    have "?P \<langle>\<langle>c, \<kappa>\<rangle>, l \<cdot> \<langle>j, f\<rangle>\<rangle>"
      using \<open>M c\<close> \<open>M \<kappa>\<close> \<open>M j\<close> \<open>M f\<close> c \<kappa> jf by blast
    then show "\<langle>\<langle>c, \<kappa>\<rangle>, l \<cdot> \<langle>j, f\<rangle>\<rangle> \<in> \<lbrace>p. ?P p\<rbrace>"
      unfolding mem using M_opair by blast
  next
    fix y
    assume "M y" and y: "\<langle>\<langle>c, \<kappa>\<rangle>, y\<rangle> \<in> \<lbrace>p. ?P p\<rbrace>"
    then have "?P \<langle>\<langle>c, \<kappa>\<rangle>, y\<rangle>"
      unfolding mem by blast
    then obtain c' \<kappa>' j' f' where "M c'" "M \<kappa>'" "M j'" "M f'"
      and eq: "\<langle>\<langle>c, \<kappa>\<rangle>, y\<rangle> = \<langle>\<langle>c', \<kappa>'\<rangle>, l \<cdot> \<langle>j', f'\<rangle>\<rangle>"
      and jf': "\<langle>j', f'\<rangle> \<in> \<kappa>'"
      by blast
    have "\<kappa>' = \<kappa>" and yeq: "y = l \<cdot> \<langle>j', f'\<rangle>"
      using eq \<open>M c\<close> \<open>M \<kappa>\<close> \<open>M y\<close> \<open>M c'\<close> \<open>M \<kappa>'\<close> by simp_all
    have \<kappa>eq: "\<kappa> = cc (cgraph C X c) \<langle>j, f\<rangle>"
      by (rule elts_member(2)[OF C ls X \<kappa> jf])
    have "conn (cgraph C X c) \<langle>j, f\<rangle> \<langle>j', f'\<rangle>"
      using jf' \<open>\<kappa>' = \<kappa>\<close> \<kappa>eq by simp
    then have "l \<cdot> \<langle>j', f'\<rangle> = l \<cdot> \<langle>j, f\<rangle>"
      by (rule cocone_conn[OF cone X C ls c M_opair])
    then show "y = l \<cdot> \<langle>j, f\<rangle>"
      using yeq by simp
  qed
qed

lemma med_cc:
  assumes C: "category C" and ls: "locally_small C" and X: "X \<in> DOb C"
    and cone: "cocone C X Q R l"
    and c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
  shows "\<lbrace>p. \<exists>\<^sub>s c \<kappa> j f. p = \<langle>\<langle>c, \<kappa>\<rangle>, l \<cdot> \<langle>j, f\<rangle>\<rangle> \<and> c \<in> Ob C \<and> \<kappa> \<in> elts C X c \<and> \<langle>j, f\<rangle> \<in> \<kappa>\<rbrace> \<cdot>
      \<langle>c, cc (cgraph C X c) \<langle>j, f\<rangle>\<rangle> = l \<cdot> \<langle>j, f\<rangle>"
proof -
  have "M j" and "M f"
    using j mem_M[OF f] by (simp_all add: mem_M)
  have v: "\<langle>j, f\<rangle> \<in> cverts C X c"
    using j f \<open>M j\<close> \<open>M f\<close> by simp
  have \<kappa>: "cc (cgraph C X c) \<langle>j, f\<rangle> \<in> elts C X c"
    by (rule elts_ccI[OF C ls X c v])
  have jf: "\<langle>j, f\<rangle> \<in> cc (cgraph C X c) \<langle>j, f\<rangle>"
    by simp
  show ?thesis
    by (rule med_app[OF C ls X cone c \<kappa> jf \<open>M j\<close> \<open>M f\<close>])
qed

text \<open>Two maps that carry the cocone of a diagram to the same cocone have the same components.\<close>

lemma mediates_agree:
  assumes C: "category C" and ls: "locally_small C" and X: "X \<in> DOb C"
    and m1: "mediates C X (inj_fun C X) l \<mu>" and m2: "mediates C X (inj_fun C X) l \<mu>'"
  shows "psh_agree C (elts_fun C X) \<mu> \<mu>'"
proof (rule psh_agreeI)
  fix c x
  assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
  have x': "x \<in> elts C X c"
    using x elts_fun_app[OF C ls X c] by simp
  obtain j f where xeq: "x = cc (cgraph C X c) \<langle>j, f\<rangle>" and j: "j \<in> Ob (ix X)"
    and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
    using x' by (rule eltsE)
  have fH: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
    using f by simp
  have xi: "x = inj_fun C X \<cdot> \<langle>j, f\<rangle>"
    unfolding inj_fun_app[OF C ls X c j fH] by (rule xeq)
  show "\<mu> \<cdot> \<langle>c, x\<rangle> = \<mu>' \<cdot> \<langle>c, x\<rangle>"
    unfolding xi mediatesD[OF m1 c j fH] mediatesD[OF m2 c j fH] by (rule refl)
qed

text \<open>The two clauses of \<open>psh_agree\<close> with \<open>act_fun\<close>, read through the beta rules.\<close>

lemma psh_agree_act_iff:
  assumes C: "category C" and ls: "locally_small C" and \<phi>: "\<phi> \<in> Hom (PSh C) X Y"
  shows "psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>) \<longleftrightarrow>
    (\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>)"
proof -
  have \<phi>P: "\<phi> \<in> PArr C"
    using \<phi> by simp
  have s: "asrc \<phi> = X"
    using \<phi> \<phi>P by simp
  have X: "X \<in> DOb C"
    using PArr_asrc[OF \<phi>P] s by simp
  show ?thesis
  proof
    assume ag: "psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>)"
    show "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>"
    proof (intro allI impI)
      fix c \<kappa>
      assume "M c" "M \<kappa>" and c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C X c"
      have \<kappa>': "\<kappa> \<in> elts C (asrc \<phi>) c"
        using \<kappa> s by simp
      have "\<kappa> \<in> elts_fun C X \<cdot> c"
        using \<kappa> elts_fun_app[OF C ls X c] by simp
      from psh_agreeD[OF ag c this] show "\<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>"
        unfolding act_fun_app[OF C ls \<phi>P c \<kappa>'] .
    qed
  next
    assume r: "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>"
    show "psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>)"
    proof (rule psh_agreeI)
      fix c x
      assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
      have x': "x \<in> elts C X c"
        using x elts_fun_app[OF C ls X c] by simp
      have x'': "x \<in> elts C (asrc \<phi>) c"
        using x' s by simp
      have "\<eta> \<cdot> \<langle>c, x\<rangle> = act C \<phi> c x"
        using r c x' mem_M[OF c] mem_M[OF x'] by blast
      then show "\<eta> \<cdot> \<langle>c, x\<rangle> = act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>"
        unfolding act_fun_app[OF C ls \<phi>P c x''] .
    qed
  qed
qed

subsection \<open>What the class functions are\<close>

theorem diagram_presheaf_reads:
  assumes "category C" and "locally_small C" and "X \<in> DOb C"
  shows "\<forall>\<^sub>s c. c \<in> Ob C \<longrightarrow> elts_fun C X \<cdot> c = elts C X c"
    and "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u) \<longrightarrow> pre_fun C X \<cdot> \<langle>u, \<kappa>\<rangle> = pre C X u \<kappa>"
    and "\<forall>\<^sub>s c j f. c \<in> Ob C \<longrightarrow> j \<in> Ob (ix X) \<longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<longrightarrow>
      inj_fun C X \<cdot> \<langle>j, f\<rangle> = cc (cgraph C X c) \<langle>j, f\<rangle>"
proof -
  show "\<forall>\<^sub>s c. c \<in> Ob C \<longrightarrow> elts_fun C X \<cdot> c = elts C X c"
    using elts_fun_app[OF assms] by blast
  show "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u) \<longrightarrow> pre_fun C X \<cdot> \<langle>u, \<kappa>\<rangle> = pre C X u \<kappa>"
    using pre_fun_app[OF assms] by blast
  show "\<forall>\<^sub>s c j f. c \<in> Ob C \<longrightarrow> j \<in> Ob (ix X) \<longrightarrow> f \<in> Hom C c (dg X \<cdot>\<^sub>o j) \<longrightarrow>
      inj_fun C X \<cdot> \<langle>j, f\<rangle> = cc (cgraph C X c) \<langle>j, f\<rangle>"
    using inj_fun_app[OF assms] by blast
qed

theorem act_fun_reads:
  assumes "category C" and "locally_small C" and "\<phi> \<in> Arr (PSh C)"
  shows "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C (asrc \<phi>) c \<longrightarrow> act_fun C \<phi> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>"
proof -
  have \<phi>: "\<phi> \<in> PArr C"
    using assms(3) by simp
  show ?thesis
    using act_fun_app[OF assms(1,2) \<phi>] by blast
qed

theorem push_reads:
  assumes "category C" and "locally_small C" and "a \<in> Arr (Diag C)"
  shows "\<forall>\<^sub>s c j f. c \<in> Ob C \<longrightarrow> j \<in> Ob (ix (asrc a)) \<longrightarrow> f \<in> Hom C c (dg (asrc a) \<cdot>\<^sub>o j) \<longrightarrow>
      push C a \<cdot> \<langle>j, f\<rangle> = cc (cgraph C (atgt a) c) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j \<circ>\<^bsub>C\<^esub> f\<rangle>"
proof -
  have a: "a \<in> DArr C"
    using assms(3) by simp
  show ?thesis
    using push_cc[OF assms(1,2) a] by blast
qed

subsection \<open>The colimit\<close>

theorem diagram_presheaf:
  assumes "category C" and "locally_small C" and "X \<in> DOb C"
  shows "presheaf C (elts_fun C X) (pre_fun C X)"
proof -
  note C = assms(1) and base = assms
  have restr: "pre_fun C X \<cdot> \<langle>u, x\<rangle> \<in> elts_fun C X \<cdot> src\<^bsub>C\<^esub> u"
    if u: "u \<in> Arr C" and x: "x \<in> elts_fun C X \<cdot> tgt\<^bsub>C\<^esub> u" for u x
  proof -
    have x': "x \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
      using x elts_fun_app[OF base cat_tgt[OF C u]] by simp
    show ?thesis
      unfolding pre_fun_app[OF base u x'] elts_fun_app[OF base cat_src[OF C u]]
      by (rule pre_elts[OF base u x'])
  qed
  have ident: "pre_fun C X \<cdot> \<langle>id\<^bsub>C\<^esub> c, x\<rangle> = x" if c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c" for c x
  proof -
    have i: "id\<^bsub>C\<^esub> c \<in> Arr C" "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c) = c"
      using C c by simp_all
    have x0: "x \<in> elts C X c"
      using x elts_fun_app[OF base c] by simp
    have x': "x \<in> elts C X (tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c))"
      using x0 i by simp
    have "pre C X (id\<^bsub>C\<^esub> c) x = x"
      by (rule elts_presheaf(3)[OF base, rule_format, OF mem_M[OF c] mem_M[OF x0] c x0])
    then show ?thesis
      using pre_fun_app[OF base i(1) x'] by simp
  qed
  have comp: "pre_fun C X \<cdot> \<langle>v \<circ>\<^bsub>C\<^esub> u, x\<rangle> = pre_fun C X \<cdot> \<langle>u, pre_fun C X \<cdot> \<langle>v, x\<rangle>\<rangle>"
    if u: "u \<in> Arr C" and v: "v \<in> Arr C" and uv: "src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u"
      and x: "x \<in> elts_fun C X \<cdot> tgt\<^bsub>C\<^esub> v" for u v x
  proof -
    have x': "x \<in> elts C X (tgt\<^bsub>C\<^esub> v)"
      using x elts_fun_app[OF base cat_tgt[OF C v]] by simp
    have vu: "v \<circ>\<^bsub>C\<^esub> u \<in> Arr C" "tgt\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u) = tgt\<^bsub>C\<^esub> v"
      using C u v uv by simp_all
    have x'': "x \<in> elts C X (tgt\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u))"
      using x' vu by simp
    have p: "pre C X v x \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
      using pre_elts[OF base v x'] uv by simp
    have e: "pre C X (v \<circ>\<^bsub>C\<^esub> u) x = pre C X u (pre C X v x)"
      by (rule elts_presheaf(4)[OF base, rule_format,
            OF mem_M[OF u] mem_M[OF v] mem_M[OF x'] u v uv x'])
    show ?thesis
      unfolding pre_fun_app[OF base vu(1) x''] pre_fun_app[OF base v x'] pre_fun_app[OF base u p]
      by (rule e)
  qed
  show ?thesis
    unfolding presheaf_def using restr ident comp by blast
qed

theorem diagram_cocone:
  assumes "category C" and "locally_small C" and "X \<in> DOb C"
  shows "cocone C X (elts_fun C X) (pre_fun C X) (inj_fun C X)"
proof -
  note C = assms(1) and base = assms
  have val: "inj_fun C X \<cdot> \<langle>j, f\<rangle> \<in> elts_fun C X \<cdot> c"
    if c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)" for c j f
  proof -
    have "\<langle>j, f\<rangle> \<in> cverts C X c"
      using j f mem_M[OF f] by (simp add: mem_M)
    then have "cc (cgraph C X c) \<langle>j, f\<rangle> \<in> elts C X c"
      by (rule elts_ccI[OF base c])
    then show ?thesis
      unfolding inj_fun_app[OF base c j f] elts_fun_app[OF base c] .
  qed
  show ?thesis
  proof (rule coconeI)
    fix c j f
    assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
    show "inj_fun C X \<cdot> \<langle>j, f\<rangle> \<in> elts_fun C X \<cdot> c"
      by (rule val[OF c j f])
  next
    fix u j f
    assume u: "u \<in> Arr C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C (tgt\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j)"
    have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
      using f by simp_all
    have su: "src\<^bsub>C\<^esub> u \<in> Ob C" and tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C"
      using C u by simp_all
    have fu: "f \<circ>\<^bsub>C\<^esub> u \<in> Hom C (src\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j)"
      using C u fa by simp
    have \<kappa>: "cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>j, f\<rangle> \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
      using val[OF tu j f] unfolding inj_fun_app[OF base tu j f] elts_fun_app[OF base tu] .
    show "inj_fun C X \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle> = pre_fun C X \<cdot> \<langle>u, inj_fun C X \<cdot> \<langle>j, f\<rangle>\<rangle>"
      unfolding inj_fun_app[OF base su j fu] inj_fun_app[OF base tu j f] pre_fun_app[OF base u \<kappa>]
      by (rule pre_cc[OF base u j fa, symmetric])
  next
    fix c b f
    assume c: "c \<in> Ob C" and b: "b \<in> Arr (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b)"
    have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b"
      using f by simp_all
    have cX: "category (ix X)"
      using assms(3) by simp
    have sb: "src\<^bsub>ix X\<^esub> b \<in> Ob (ix X)" and tb: "tgt\<^bsub>ix X\<^esub> b \<in> Ob (ix X)"
      using cX b by simp_all
    have Fbf: "dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f \<in> Hom C c (dg X \<cdot>\<^sub>o tgt\<^bsub>ix X\<^esub> b)"
      using C assms(3) b fa by simp
    have e: "\<langle>\<langle>src\<^bsub>ix X\<^esub> b, f\<rangle>, \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>\<rangle> \<in> cgraph C X c"
      by (rule comma_edgesI[OF b fa])
    have "conn (cgraph C X c) \<langle>src\<^bsub>ix X\<^esub> b, f\<rangle> \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule conn_edge[OF e M_opair M_opair])
    then have "cc (cgraph C X c) \<langle>src\<^bsub>ix X\<^esub> b, f\<rangle> = cc (cgraph C X c) \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule cc_eq[OF M_cgraph[OF base c] M_opair])
    then show "inj_fun C X \<cdot> \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle> = inj_fun C X \<cdot> \<langle>src\<^bsub>ix X\<^esub> b, f\<rangle>"
      unfolding inj_fun_app[OF base c tb Fbf] inj_fun_app[OF base c sb f] by (rule sym)
  qed
qed

text \<open>
  The universal property. Given a cocone \<open>l\<close> with vertex \<open>(Q, R)\<close>, the map sends the component
  of \<open>\<langle>j, f\<rangle>\<close> to \<open>l \<cdot> \<langle>j, f\<rangle>\<close>. This does not depend on the vertex chosen in the component,
  because \<open>l\<close> takes the same value at the two ends of every edge of the comma graph, by the
  third clause of \<open>cocone\<close>.
\<close>

theorem diagram_colimit:
  assumes "category C" and "locally_small C" and "X \<in> DOb C"
  shows "colimiting C X (elts_fun C X) (pre_fun C X) (inj_fun C X)"
proof (rule colimitingI[OF diagram_presheaf[OF assms] diagram_cocone[OF assms]])
  note C = assms(1) and ls = assms(2) and X = assms(3) and base = assms
  fix Q' R' l'
  assume "presheaf C Q' R'" and cone: "cocone C X Q' R' l'"
  define mu where "mu = \<lbrace>p. \<exists>\<^sub>s c \<kappa> j f. p = \<langle>\<langle>c, \<kappa>\<rangle>, l' \<cdot> \<langle>j, f\<rangle>\<rangle> \<and> c \<in> Ob C \<and> \<kappa> \<in> elts C X c \<and> \<langle>j, f\<rangle> \<in> \<kappa>\<rbrace>"
  note mcc = med_cc[OF C ls X cone, folded mu_def]
  have map: "psh_map C (elts_fun C X) (pre_fun C X) Q' R' mu"
  proof (rule psh_mapI)
    fix c x
    assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
    have x': "x \<in> elts C X c"
      using x elts_fun_app[OF base c] by simp
    obtain j f where xeq: "x = cc (cgraph C X c) \<langle>j, f\<rangle>" and j: "j \<in> Ob (ix X)"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
      using x' by (rule eltsE)
    have fH: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
      using f by simp
    show "mu \<cdot> \<langle>c, x\<rangle> \<in> Q' \<cdot> c"
      unfolding xeq mcc[OF c j fH] by (rule cocone_val[OF cone c j fH])
  next
    fix u x
    assume u: "u \<in> Arr C" and x: "x \<in> elts_fun C X \<cdot> tgt\<^bsub>C\<^esub> u"
    have tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C" and su: "src\<^bsub>C\<^esub> u \<in> Ob C"
      using C u by simp_all
    have x': "x \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
      using x elts_fun_app[OF base tu] by simp
    obtain j f where xeq: "x = cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>j, f\<rangle>" and j: "j \<in> Ob (ix X)"
      and f: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
      using x' by (rule eltsE)
    have fH: "f \<in> Hom C (tgt\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j)"
      using f by simp
    have fuH: "f \<circ>\<^bsub>C\<^esub> u \<in> Hom C (src\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j)"
      using C u f by simp
    have x'': "cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>j, f\<rangle> \<in> elts C X (tgt\<^bsub>C\<^esub> u)"
      using x' unfolding xeq .
    have pre: "pre_fun C X \<cdot> \<langle>u, cc (cgraph C X (tgt\<^bsub>C\<^esub> u)) \<langle>j, f\<rangle>\<rangle> =
        cc (cgraph C X (src\<^bsub>C\<^esub> u)) \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle>"
      unfolding pre_fun_app[OF base u x''] by (rule pre_cc[OF base u j f])
    show "mu \<cdot> \<langle>src\<^bsub>C\<^esub> u, pre_fun C X \<cdot> \<langle>u, x\<rangle>\<rangle> = R' \<cdot> \<langle>u, mu \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>"
      unfolding xeq pre mcc[OF su j fuH] mcc[OF tu j fH] by (rule cocone_nat[OF cone u j fH])
  qed
  have med: "mediates C X (inj_fun C X) l' mu"
  proof (rule mediatesI)
    fix c j f
    assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
    show "mu \<cdot> \<langle>c, inj_fun C X \<cdot> \<langle>j, f\<rangle>\<rangle> = l' \<cdot> \<langle>j, f\<rangle>"
      unfolding inj_fun_app[OF base c j f] by (rule mcc[OF c j f])
  qed
  show "\<exists>\<mu>. psh_map C (elts_fun C X) (pre_fun C X) Q' R' \<mu> \<and> mediates C X (inj_fun C X) l' \<mu>"
    using map med by blast
qed (rule mediates_agree[OF assms]; assumption)

subsection \<open>The small presheaves are the presheaves of diagrams\<close>

corollary diagram_presheaf_small:
  assumes "category C" and "locally_small C" and "X \<in> DOb C"
  shows "small_presheaf C (elts_fun C X) (pre_fun C X)"
  unfolding small_presheaf_def using assms(3) diagram_colimit[OF assms] by blast

text \<open>A colimit is unique up to isomorphism: the usual argument, with the two mediating maps.\<close>

theorem colimit_is_diagram_presheaf:
  assumes "category C" and "locally_small C" and "X \<in> DOb C" and "colimiting C X Q R l"
  shows "psh_iso C (elts_fun C X) (pre_fun C X) Q R"
proof -
  note C = assms(1) and base = assms(1-3) and lim = assms(4)
  let ?E = "elts_fun C X" and ?P = "pre_fun C X" and ?I = "inj_fun C X"
  have dlim: "colimiting C X ?E ?P ?I"
    by (rule diagram_colimit[OF base])
  have pE: "presheaf C ?E ?P"
    by (rule diagram_presheaf[OF base])
  have cE: "cocone C X ?E ?P ?I"
    by (rule diagram_cocone[OF base])
  have pQ: "presheaf C Q R"
    by (rule colimiting_presheaf[OF lim])
  have cQ: "cocone C X Q R l"
    by (rule colimiting_cocone[OF lim])
  obtain \<mu> where \<mu>: "psh_map C ?E ?P Q R \<mu>" and m\<mu>: "mediates C X ?I l \<mu>"
    using colimiting_ex[OF dlim pQ cQ] by blast
  obtain \<nu> where \<nu>: "psh_map C Q R ?E ?P \<nu>" and m\<nu>: "mediates C X l ?I \<nu>"
    using colimiting_ex[OF lim pE cE] by blast
  have a1: "psh_agree C ?E (\<lambda>p\<in>\<V>. \<nu> \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) (\<lambda>p\<in>\<V>. psnd p)"
    by (rule colimiting_unique[OF dlim pE cE psh_map_comp[OF C \<mu> \<nu>] mediates_comp[OF m\<mu> m\<nu>]
          psh_map_id mediates_id])
  have a2: "psh_agree C Q (\<lambda>p\<in>\<V>. \<mu> \<cdot> \<langle>pfst p, \<nu> \<cdot> p\<rangle>) (\<lambda>p\<in>\<V>. psnd p)"
    by (rule colimiting_unique[OF lim pQ cQ psh_map_comp[OF C \<nu> \<mu>] mediates_comp[OF m\<nu> m\<mu>]
          psh_map_id mediates_id])
  have inv1: "\<nu> \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x" if c: "c \<in> Ob C" and x: "x \<in> ?E \<cdot> c" for c x
    using psh_agreeD[OF a1 c x]
    unfolding app_comp_Lam[OF mem_M[OF c] mem_M[OF x]] app_id_Lam[OF mem_M[OF c] mem_M[OF x]] .
  have inv2: "\<mu> \<cdot> \<langle>c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x" if c: "c \<in> Ob C" and x: "x \<in> Q \<cdot> c" for c x
    using psh_agreeD[OF a2 c x]
    unfolding app_comp_Lam[OF mem_M[OF c] mem_M[OF x]] app_id_Lam[OF mem_M[OF c] mem_M[OF x]] .
  show ?thesis
    unfolding psh_iso_def using \<mu> \<nu> inv1 inv2 by blast
qed

corollary small_presheaf_is_diagram_presheaf:
  assumes "category C" and "locally_small C" and "small_presheaf C Q R"
  shows "\<exists>\<^sub>s X. X \<in> DOb C \<and> psh_iso C (elts_fun C X) (pre_fun C X) Q R"
proof -
  obtain X l where X: "X \<in> DOb C" and lim: "colimiting C X Q R l"
    using assms(3) unfolding small_presheaf_def by blast
  have "psh_iso C (elts_fun C X) (pre_fun C X) Q R"
    by (rule colimit_is_diagram_presheaf[OF assms(1,2) X lim])
  then show ?thesis
    using X mem_M[OF X] by blast
qed

subsection \<open>Arrows of \<open>PSh C\<close> are the maps of presheaves\<close>

text \<open>The theorems of \<open>Adequacy\<close> in the vocabulary of this theory.\<close>

theorem arrow_is_psh_map:
  assumes "category C" and "locally_small C" and "\<phi> \<in> Arr (PSh C)"
  shows "psh_map C (elts_fun C (asrc \<phi>)) (pre_fun C (asrc \<phi>))
    (elts_fun C (atgt \<phi>)) (pre_fun C (atgt \<phi>)) (act_fun C \<phi>)"
proof -
  note C = assms(1) and ls = assms(2)
  have \<phi>: "\<phi> \<in> PArr C"
    using assms(3) by simp
  have X: "asrc \<phi> \<in> DOb C" and Y: "atgt \<phi> \<in> DOb C"
    using \<phi> by simp_all
  show ?thesis
  proof (rule psh_mapI)
    fix c x
    assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C (asrc \<phi>) \<cdot> c"
    have x': "x \<in> elts C (asrc \<phi>) c"
      using x elts_fun_app[OF C ls X c] by simp
    show "act_fun C \<phi> \<cdot> \<langle>c, x\<rangle> \<in> elts_fun C (atgt \<phi>) \<cdot> c"
      unfolding act_fun_app[OF C ls \<phi> c x'] elts_fun_app[OF C ls Y c]
      by (rule act_elts[OF C ls \<phi> x'])
  next
    fix u x
    assume u: "u \<in> Arr C" and x: "x \<in> elts_fun C (asrc \<phi>) \<cdot> tgt\<^bsub>C\<^esub> u"
    have su: "src\<^bsub>C\<^esub> u \<in> Ob C" and tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C"
      using C u by simp_all
    have x': "x \<in> elts C (asrc \<phi>) (tgt\<^bsub>C\<^esub> u)"
      using x elts_fun_app[OF C ls X tu] by simp
    have p: "pre C (asrc \<phi>) u x \<in> elts C (asrc \<phi>) (src\<^bsub>C\<^esub> u)"
      by (rule pre_elts[OF C ls X u x'])
    have a: "act C \<phi> (tgt\<^bsub>C\<^esub> u) x \<in> elts C (atgt \<phi>) (tgt\<^bsub>C\<^esub> u)"
      by (rule act_elts[OF C ls \<phi> x'])
    have nat: "act C \<phi> (src\<^bsub>C\<^esub> u) (pre C (asrc \<phi>) u x) = pre C (atgt \<phi>) u (act C \<phi> (tgt\<^bsub>C\<^esub> u) x)"
      by (rule act_natural(2)[OF assms, rule_format, OF mem_M[OF u] mem_M[OF x'] u x'])
    show "act_fun C \<phi> \<cdot> \<langle>src\<^bsub>C\<^esub> u, pre_fun C (asrc \<phi>) \<cdot> \<langle>u, x\<rangle>\<rangle> =
        pre_fun C (atgt \<phi>) \<cdot> \<langle>u, act_fun C \<phi> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>"
      unfolding pre_fun_app[OF C ls X u x'] act_fun_app[OF C ls \<phi> su p]
        act_fun_app[OF C ls \<phi> tu x'] pre_fun_app[OF C ls Y u a]
      by (rule nat)
  qed
qed

theorem psh_map_is_arrow:
  assumes "category C" and "locally_small C" and "X \<in> DOb C" and "Y \<in> DOb C"
    and "psh_map C (elts_fun C X) (pre_fun C X) (elts_fun C Y) (pre_fun C Y) \<eta>"
  shows "\<exists>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<and> psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>) \<and>
      (\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>') \<longrightarrow> \<phi>' = \<phi>)"
proof -
  note C = assms(1) and ls = assms(2) and X = assms(3) and Y = assms(4) and \<eta> = assms(5)
  have h1: "\<eta> \<cdot> \<langle>c, \<kappa>\<rangle> \<in> elts C Y c" if c: "c \<in> Ob C" and \<kappa>: "\<kappa> \<in> elts C X c" for c \<kappa>
  proof -
    have "\<kappa> \<in> elts_fun C X \<cdot> c"
      using \<kappa> elts_fun_app[OF C ls X c] by simp
    from psh_map_val[OF \<eta> c this] show ?thesis
      unfolding elts_fun_app[OF C ls Y c] .
  qed
  have h2: "\<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> u, pre C X u \<kappa>\<rangle> = pre C Y u (\<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, \<kappa>\<rangle>)"
    if u: "u \<in> Arr C" and \<kappa>: "\<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u)" for u \<kappa>
  proof -
    have tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C"
      using C u by simp
    have \<kappa>': "\<kappa> \<in> elts_fun C X \<cdot> tgt\<^bsub>C\<^esub> u"
      using \<kappa> elts_fun_app[OF C ls X tu] by simp
    have e: "\<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, \<kappa>\<rangle> \<in> elts C Y (tgt\<^bsub>C\<^esub> u)"
      by (rule h1[OF tu \<kappa>])
    from psh_map_nat[OF \<eta> u \<kappa>'] show ?thesis
      unfolding pre_fun_app[OF C ls X u \<kappa>] pre_fun_app[OF C ls Y u e] .
  qed
  have H1: "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> \<in> elts C Y c"
    using h1 by blast
  have H2: "\<forall>\<^sub>s u \<kappa>. u \<in> Arr C \<longrightarrow> \<kappa> \<in> elts C X (tgt\<^bsub>C\<^esub> u) \<longrightarrow>
      \<eta> \<cdot> \<langle>src\<^bsub>C\<^esub> u, pre C X u \<kappa>\<rangle> = pre C Y u (\<eta> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, \<kappa>\<rangle>)"
    using h2 by blast
  obtain \<phi> where "M \<phi>" and hom: "\<phi> \<in> Hom (PSh C) X Y"
    and rep: "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi> c \<kappa>"
    and uniq: "\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow>
      (\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi>' c \<kappa>) \<longrightarrow> \<phi>' = \<phi>"
    using act_full_and_faithful[OF C ls X Y H1 H2] by blast
  have ag: "psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>)"
    using psh_agree_act_iff[OF C ls hom] rep by blast
  have un: "\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>') \<longrightarrow> \<phi>' = \<phi>"
  proof (intro allI impI)
    fix \<phi>'
    assume "M \<phi>'" and h': "\<phi>' \<in> Hom (PSh C) X Y" and a': "psh_agree C (elts_fun C X) \<eta> (act_fun C \<phi>')"
    have "\<forall>\<^sub>s c \<kappa>. c \<in> Ob C \<longrightarrow> \<kappa> \<in> elts C X c \<longrightarrow> \<eta> \<cdot> \<langle>c, \<kappa>\<rangle> = act C \<phi>' c \<kappa>"
      using psh_agree_act_iff[OF C ls h'] a' by blast
    then show "\<phi>' = \<phi>"
      using uniq \<open>M \<phi>'\<close> h' by blast
  qed
  show ?thesis
    using \<open>M \<phi>\<close> hom ag un by blast
qed

subsection \<open>The colimit functor is the induced map of colimits\<close>

text \<open>
  For a morphism \<open>a\<close> of diagrams, \<open>push C a\<close> is a cocone, and the map of \<open>colim_functor C \<cdot>\<^sub>a a\<close>
  carries the colimit cocone of the source to it. By \<open>diagram_colimit\<close> it is the only map of
  presheaves that does.
\<close>

theorem colim_functor_induced:
  assumes "category C" and "locally_small C" and "a \<in> Arr (Diag C)"
  shows "cocone C (asrc a) (elts_fun C (atgt a)) (pre_fun C (atgt a)) (push C a)"
    and "psh_map C (elts_fun C (asrc a)) (pre_fun C (asrc a))
      (elts_fun C (atgt a)) (pre_fun C (atgt a)) (act_fun C (colim_functor C \<cdot>\<^sub>a a))"
    and "mediates C (asrc a) (inj_fun C (asrc a)) (push C a) (act_fun C (colim_functor C \<cdot>\<^sub>a a))"
proof -
  note C = assms(1) and ls = assms(2)
  have a: "a \<in> DArr C"
    using assms(3) by simp
  let ?X = "asrc a" and ?Y = "atgt a" and ?p = "afun a" and ?\<alpha> = "anat a"
  have X: "?X \<in> DOb C" and Y: "?Y \<in> DOb C"
    using a by simp_all
  have cX: "category (ix ?X)"
    using a by simp
  have pF: "is_functor ?p (ix ?X) (ix ?Y)"
    by (rule DArr_functor[OF a])
  have cone: "cocone C ?Y (elts_fun C ?Y) (pre_fun C ?Y) (inj_fun C ?Y)"
    by (rule diagram_cocone[OF C ls Y])
  have pj: "?p \<cdot>\<^sub>o j \<in> Ob (ix ?Y)" if "j \<in> Ob (ix ?X)" for j
    using pF that by simp
  have \<alpha>f: "?\<alpha> \<cdot> j \<circ>\<^bsub>C\<^esub> f \<in> Hom C c (dg ?Y \<cdot>\<^sub>o (?p \<cdot>\<^sub>o j))"
    if j: "j \<in> Ob (ix ?X)" and f: "f \<in> Hom C c (dg ?X \<cdot>\<^sub>o j)" for c j f
    using C a j f by simp
  have push: "push C a \<cdot> \<langle>j, f\<rangle> = inj_fun C ?Y \<cdot> \<langle>?p \<cdot>\<^sub>o j, ?\<alpha> \<cdot> j \<circ>\<^bsub>C\<^esub> f\<rangle>"
    if j: "j \<in> Ob (ix ?X)" and f: "f \<in> Hom C c (dg ?X \<cdot>\<^sub>o j)" for c j f
    by (rule push_app[OF a j]) (use f in simp_all)
  show "cocone C ?X (elts_fun C ?Y) (pre_fun C ?Y) (push C a)"
  proof (rule coconeI)
    fix c j f
    assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix ?X)" and f: "f \<in> Hom C c (dg ?X \<cdot>\<^sub>o j)"
    show "push C a \<cdot> \<langle>j, f\<rangle> \<in> elts_fun C ?Y \<cdot> c"
      unfolding push[OF j f] by (rule cocone_val[OF cone c pj[OF j] \<alpha>f[OF j f]])
  next
    fix u j f
    assume u: "u \<in> Arr C" and j: "j \<in> Ob (ix ?X)" and f: "f \<in> Hom C (tgt\<^bsub>C\<^esub> u) (dg ?X \<cdot>\<^sub>o j)"
    have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg ?X \<cdot>\<^sub>o j"
      using f by simp_all
    have fu: "f \<circ>\<^bsub>C\<^esub> u \<in> Hom C (src\<^bsub>C\<^esub> u) (dg ?X \<cdot>\<^sub>o j)"
      using C u fa by simp
    have assoc: "?\<alpha> \<cdot> j \<circ>\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> u) = (?\<alpha> \<cdot> j \<circ>\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> u"
      by (rule cat_assoc[OF C u fa(1) _ fa(2)]) (use a j fa in simp_all)
    show "push C a \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle> = pre_fun C ?Y \<cdot> \<langle>u, push C a \<cdot> \<langle>j, f\<rangle>\<rangle>"
      unfolding push[OF j fu] push[OF j f] assoc
      by (rule cocone_nat[OF cone u pj[OF j] \<alpha>f[OF j f]])
  next
    fix c b f
    assume c: "c \<in> Ob C" and b: "b \<in> Arr (ix ?X)" and f: "f \<in> Hom C c (dg ?X \<cdot>\<^sub>o src\<^bsub>ix ?X\<^esub> b)"
    let ?s = "src\<^bsub>ix ?X\<^esub> b" and ?t = "tgt\<^bsub>ix ?X\<^esub> b"
    have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg ?X \<cdot>\<^sub>o ?s"
      using f by simp_all
    have s: "?s \<in> Ob (ix ?X)" and t: "?t \<in> Ob (ix ?X)"
      using cX b by simp_all
    have Fb: "dg ?X \<cdot>\<^sub>a b \<in> Arr C" "src\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>a b) = dg ?X \<cdot>\<^sub>o ?s"
      "tgt\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>a b) = dg ?X \<cdot>\<^sub>o ?t"
      using X b by simp_all
    have Fbf: "dg ?X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f \<in> Hom C c (dg ?X \<cdot>\<^sub>o ?t)"
      using C Fb fa by simp
    have pb: "?p \<cdot>\<^sub>a b \<in> Arr (ix ?Y)" "src\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a b) = ?p \<cdot>\<^sub>o ?s"
      "tgt\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a b) = ?p \<cdot>\<^sub>o ?t"
      using pF b by simp_all
    have \<alpha>s: "?\<alpha> \<cdot> ?s \<in> Arr C" "src\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?s) = dg ?X \<cdot>\<^sub>o ?s"
      "tgt\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?s) = dg ?Y \<cdot>\<^sub>o (?p \<cdot>\<^sub>o ?s)"
      using a s by simp_all
    have \<alpha>t: "?\<alpha> \<cdot> ?t \<in> Arr C" "src\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?t) = dg ?X \<cdot>\<^sub>o ?t"
      using a t by simp_all
    have Gpb: "dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a b) \<in> Arr C" "src\<^bsub>C\<^esub> (dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a b)) = dg ?Y \<cdot>\<^sub>o (?p \<cdot>\<^sub>o ?s)"
      using Y pb by simp_all
    have nat: "?\<alpha> \<cdot> ?t \<circ>\<^bsub>C\<^esub> dg ?X \<cdot>\<^sub>a b = dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a b) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s"
      by (rule DArr_anat_nat[OF a b])
    have "?\<alpha> \<cdot> ?t \<circ>\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f) = (?\<alpha> \<cdot> ?t \<circ>\<^bsub>C\<^esub> dg ?X \<cdot>\<^sub>a b) \<circ>\<^bsub>C\<^esub> f"
      by (rule cat_assoc[OF C fa(1) Fb(1) \<alpha>t(1)]) (simp_all add: fa Fb \<alpha>t)
    also have "\<dots> = (dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a b) \<circ>\<^bsub>C\<^esub> ?\<alpha> \<cdot> ?s) \<circ>\<^bsub>C\<^esub> f"
      unfolding nat by (rule refl)
    also have "\<dots> = dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a b) \<circ>\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?s \<circ>\<^bsub>C\<^esub> f)"
      by (rule cat_assoc[OF C fa(1) \<alpha>s(1) Gpb(1), symmetric]) (simp_all add: fa \<alpha>s Gpb)
    finally have e: "?\<alpha> \<cdot> ?t \<circ>\<^bsub>C\<^esub> (dg ?X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f) = dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a b) \<circ>\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?s \<circ>\<^bsub>C\<^esub> f)" .
    have \<alpha>sf: "?\<alpha> \<cdot> ?s \<circ>\<^bsub>C\<^esub> f \<in> Hom C c (dg ?Y \<cdot>\<^sub>o src\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a b))"
      using \<alpha>f[OF s f] pb(2) by simp
    have "inj_fun C ?Y \<cdot> \<langle>tgt\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a b), dg ?Y \<cdot>\<^sub>a (?p \<cdot>\<^sub>a b) \<circ>\<^bsub>C\<^esub> (?\<alpha> \<cdot> ?s \<circ>\<^bsub>C\<^esub> f)\<rangle> =
        inj_fun C ?Y \<cdot> \<langle>src\<^bsub>ix ?Y\<^esub> (?p \<cdot>\<^sub>a b), ?\<alpha> \<cdot> ?s \<circ>\<^bsub>C\<^esub> f\<rangle>"
      by (rule cocone_compat[OF cone c pb(1) \<alpha>sf])
    then show "push C a \<cdot> \<langle>?t, dg ?X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle> = push C a \<cdot> \<langle>?s, f\<rangle>"
      unfolding push[OF t Fbf] push[OF s f] e pb(2,3) .
  qed
  have \<phi>A: "colim_functor C \<cdot>\<^sub>a a \<in> Arr (PSh C)"
    using C ls a by simp
  have \<phi>P: "colim_functor C \<cdot>\<^sub>a a \<in> PArr C"
    using C ls a by simp
  show "psh_map C (elts_fun C ?X) (pre_fun C ?X) (elts_fun C ?Y) (pre_fun C ?Y)
      (act_fun C (colim_functor C \<cdot>\<^sub>a a))"
    using arrow_is_psh_map[OF C ls \<phi>A] a by simp
  show "mediates C ?X (inj_fun C ?X) (push C a) (act_fun C (colim_functor C \<cdot>\<^sub>a a))"
  proof (rule mediatesI)
    fix c j f
    assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix ?X)" and f: "f \<in> Hom C c (dg ?X \<cdot>\<^sub>o j)"
    have v: "\<langle>j, f\<rangle> \<in> cverts C ?X c"
      using j f mem_M[OF f] by (simp add: mem_M)
    have \<kappa>: "cc (cgraph C ?X c) \<langle>j, f\<rangle> \<in> elts C (asrc (colim_functor C \<cdot>\<^sub>a a)) c"
      using elts_ccI[OF C ls X c v] a by simp
    show "act_fun C (colim_functor C \<cdot>\<^sub>a a) \<cdot> \<langle>c, inj_fun C ?X \<cdot> \<langle>j, f\<rangle>\<rangle> = push C a \<cdot> \<langle>j, f\<rangle>"
      unfolding inj_fun_app[OF C ls X c j f] act_fun_app[OF C ls \<phi>P c \<kappa>]
        act_colim_functor[OF C ls assms(3) c j f] push_cc[OF C ls a c j f]
      by (rule refl)
  qed
qed

subsection \<open>One-object diagrams give the representable presheaves\<close>

text \<open>
  The elements of the presheaf of \<open>point C x\<close> at \<open>c\<close> are the arrows \<open>c \<rightarrow> x\<close>: each arrow gives an
  element, and each element comes from exactly one arrow.
\<close>

theorem point_representable:
  assumes "category C" and "locally_small C" and "x \<in> Ob C" and "c \<in> Ob C"
  shows "\<forall>\<^sub>s f. f \<in> Hom C c x \<longrightarrow> cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle> \<in> elts C (point C x) c"
    and "\<forall>\<^sub>s \<kappa>. \<kappa> \<in> elts C (point C x) c \<longrightarrow>
      (\<exists>\<^sub>s f. f \<in> Hom C c x \<and> \<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle> \<and>
        (\<forall>\<^sub>s f'. f' \<in> Hom C c x \<longrightarrow> \<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f'\<rangle> \<longrightarrow> f' = f))"
proof -
  note C = assms(1) and ls = assms(2) and x = assms(3) and c = assms(4)
  have P: "point C x \<in> DOb C"
    using C x by simp
  have "M x"
    using x by (rule mem_M)
  have cc_elts: "cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle> \<in> elts C (point C x) c"
    if f: "f \<in> Hom C c x" for f
  proof -
    have "\<langle>\<emptyset>, f\<rangle> \<in> cverts C (point C x) c"
      using f mem_M[OF f] \<open>M x\<close> by (simp add: mem_M)
    then show ?thesis
      by (rule elts_ccI[OF C ls P c])
  qed
  have uniq: "f' = f"
    if f: "f \<in> Hom C c x" and f': "f' \<in> Hom C c x"
      and eq: "cc (cgraph C (point C x) c) \<langle>\<emptyset>, f'\<rangle> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle>" for f f'
  proof -
    have "\<langle>\<emptyset>, f'\<rangle> \<in> cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle>"
      unfolding eq[symmetric] by simp
    then have "conn (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle> \<langle>\<emptyset>, f'\<rangle>"
      by simp
    then have "\<langle>\<emptyset>, f'\<rangle> = \<langle>\<emptyset>, f\<rangle>"
      by (rule point_conn[OF C x M_opair])
    then show ?thesis
      using mem_M[OF f] mem_M[OF f'] by simp
  qed
  show "\<forall>\<^sub>s f. f \<in> Hom C c x \<longrightarrow> cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle> \<in> elts C (point C x) c"
    using cc_elts by blast
  show "\<forall>\<^sub>s \<kappa>. \<kappa> \<in> elts C (point C x) c \<longrightarrow>
      (\<exists>\<^sub>s f. f \<in> Hom C c x \<and> \<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle> \<and>
        (\<forall>\<^sub>s f'. f' \<in> Hom C c x \<longrightarrow> \<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f'\<rangle> \<longrightarrow> f' = f))"
  proof (intro allI impI)
    fix \<kappa>
    assume "M \<kappa>" and \<kappa>: "\<kappa> \<in> elts C (point C x) c"
    obtain k f where \<kappa>eq: "\<kappa> = cc (cgraph C (point C x) c) \<langle>k, f\<rangle>" and k: "k \<in> Ob (ix (point C x))"
      and fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg (point C x) \<cdot>\<^sub>o k"
      using \<kappa> by (rule eltsE)
    have k0: "k = \<emptyset>"
      using k by simp
    have fH: "f \<in> Hom C c x"
      using fa k0 \<open>M x\<close> by simp
    have \<kappa>eq': "\<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle>"
      using \<kappa>eq k0 by simp
    have u: "f' = f" if f': "f' \<in> Hom C c x" and e: "\<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f'\<rangle>"
      for f'
    proof -
      have "cc (cgraph C (point C x) c) \<langle>\<emptyset>, f'\<rangle> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle>"
        using e \<kappa>eq' by simp
      then show ?thesis
        by (rule uniq[OF fH f'])
    qed
    show "\<exists>\<^sub>s f. f \<in> Hom C c x \<and> \<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f\<rangle> \<and>
        (\<forall>\<^sub>s f'. f' \<in> Hom C c x \<longrightarrow> \<kappa> = cc (cgraph C (point C x) c) \<langle>\<emptyset>, f'\<rangle> \<longrightarrow> f' = f)"
      using mem_M[OF fa(1)] fH \<kappa>eq' u by blast
  qed
qed

subsection \<open>Arbitrary small presheaves\<close>

text \<open>
  The theorems so far are about the presheaves \<open>elts_fun C X\<close> of the objects of \<open>PSh C\<close>. This
  part carries them to an arbitrary small presheaf \<open>(Q, R)\<close>. A presheaf isomorphic to a small
  one is small. And if \<open>X\<close> and \<open>Y\<close> are objects of \<open>PSh C\<close> whose presheaves are isomorphic to
  \<open>(Q, R)\<close> and \<open>(Q', R')\<close>, then the maps \<open>(Q, R) \<rightarrow> (Q', R')\<close>, up to having the same components,
  are the arrows \<open>X \<rightarrow> Y\<close> of \<open>PSh C\<close>, compatibly with identities and composition. Such \<open>X\<close> and
  \<open>Y\<close> exist for every two small presheaves.

  \<open>psh_inverse C Q R Q' R' \<mu> \<nu>\<close>: the maps \<open>\<mu> : (Q, R) \<rightarrow> (Q', R')\<close> and \<open>\<nu>\<close> back are inverse to
  each other. So \<open>psh_iso\<close> says that such a pair exists.
\<close>

definition psh_inverse :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "psh_inverse C Q R Q' R' \<mu> \<nu> \<longleftrightarrow>
    psh_map C Q R Q' R' \<mu> \<and> psh_map C Q' R' Q R \<nu> \<and>
    (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> Q \<cdot> c \<longrightarrow> \<nu> \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x) \<and>
    (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> Q' \<cdot> c \<longrightarrow> \<mu> \<cdot> \<langle>c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x)"

text \<open>
  \<open>psh_square C X \<alpha> \<beta> \<eta> \<phi>\<close>, for an arrow \<open>\<phi> : X \<rightarrow> Y\<close> of \<open>PSh C\<close>, a map \<open>\<alpha>\<close> out of the presheaf
  of \<open>X\<close>, a map \<open>\<beta>\<close> out of the presheaf of \<open>Y\<close>, and a map \<open>\<eta>\<close> from the target of \<open>\<alpha>\<close> to the
  target of \<open>\<beta>\<close>: the square commutes, that is \<open>\<eta> \<circ> \<alpha> = \<beta> \<circ> act_fun C \<phi>\<close>. The definition does
  not ask that \<open>\<phi>\<close> is an arrow out of \<open>X\<close>; every statement below that uses it has a hypothesis
  that says so.
\<close>

definition psh_square :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "psh_square C X \<alpha> \<beta> \<eta> \<phi> \<longleftrightarrow>
    (\<forall>\<^sub>s c x. c \<in> Ob C \<longrightarrow> x \<in> elts_fun C X \<cdot> c \<longrightarrow>
      \<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>)"

theorem psh_iso_iff: "psh_iso C Q R Q' R' \<longleftrightarrow> (\<exists>\<mu> \<nu>. psh_inverse C Q R Q' R' \<mu> \<nu>)"
  unfolding psh_iso_def psh_inverse_def by (rule refl)

text \<open>
  Reading rules for \<open>psh_inverse\<close>, \<open>psh_square\<close> and \<open>presheaf\<close>, without \<open>\<forall>\<^sub>s\<close>; and the map
  of presheaves given by an arrow \<open>X \<rightarrow> Y\<close> of \<open>PSh C\<close>.
\<close>

lemma psh_inverse_map1: "psh_inverse C Q R Q' R' \<mu> \<nu> \<Longrightarrow> psh_map C Q R Q' R' \<mu>"
  unfolding psh_inverse_def by blast

lemma psh_inverse_map2: "psh_inverse C Q R Q' R' \<mu> \<nu> \<Longrightarrow> psh_map C Q' R' Q R \<nu>"
  unfolding psh_inverse_def by blast

lemma psh_inverse_inv1:
  assumes "psh_inverse C Q R Q' R' \<mu> \<nu>" and "c \<in> Ob C" and "x \<in> Q \<cdot> c"
  shows "\<nu> \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding psh_inverse_def by blast

lemma psh_inverse_inv2:
  assumes "psh_inverse C Q R Q' R' \<mu> \<nu>" and "c \<in> Ob C" and "x \<in> Q' \<cdot> c"
  shows "\<mu> \<cdot> \<langle>c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle> = x"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding psh_inverse_def by blast

lemma psh_squareI:
  assumes "\<And>c x. c \<in> Ob C \<Longrightarrow> x \<in> elts_fun C X \<cdot> c \<Longrightarrow>
    \<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>"
  shows "psh_square C X \<alpha> \<beta> \<eta> \<phi>"
  unfolding psh_square_def using assms by blast

lemma psh_squareD:
  assumes "psh_square C X \<alpha> \<beta> \<eta> \<phi>" and "c \<in> Ob C" and "x \<in> elts_fun C X \<cdot> c"
  shows "\<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding psh_square_def by blast

lemma presheafI:
  assumes "\<And>u x. u \<in> Arr C \<Longrightarrow> x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u \<Longrightarrow> R \<cdot> \<langle>u, x\<rangle> \<in> Q \<cdot> src\<^bsub>C\<^esub> u"
    and "\<And>c x. c \<in> Ob C \<Longrightarrow> x \<in> Q \<cdot> c \<Longrightarrow> R \<cdot> \<langle>id\<^bsub>C\<^esub> c, x\<rangle> = x"
    and "\<And>u v x. u \<in> Arr C \<Longrightarrow> v \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u \<Longrightarrow> x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> v \<Longrightarrow>
      R \<cdot> \<langle>v \<circ>\<^bsub>C\<^esub> u, x\<rangle> = R \<cdot> \<langle>u, R \<cdot> \<langle>v, x\<rangle>\<rangle>"
  shows "presheaf C Q R"
  unfolding presheaf_def using assms by blast

lemma presheaf_restr:
  assumes "presheaf C Q R" and "u \<in> Arr C" and "x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u"
  shows "R \<cdot> \<langle>u, x\<rangle> \<in> Q \<cdot> src\<^bsub>C\<^esub> u"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding presheaf_def by blast

lemma presheaf_id:
  assumes "presheaf C Q R" and "c \<in> Ob C" and "x \<in> Q \<cdot> c"
  shows "R \<cdot> \<langle>id\<^bsub>C\<^esub> c, x\<rangle> = x"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] unfolding presheaf_def by blast

lemma presheaf_comp:
  assumes "presheaf C Q R" and "u \<in> Arr C" and "v \<in> Arr C" and "src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u"
    and "x \<in> Q \<cdot> tgt\<^bsub>C\<^esub> v"
  shows "R \<cdot> \<langle>v \<circ>\<^bsub>C\<^esub> u, x\<rangle> = R \<cdot> \<langle>u, R \<cdot> \<langle>v, x\<rangle>\<rangle>"
  using assms mem_M[OF assms(2)] mem_M[OF assms(3)] mem_M[OF assms(5)] unfolding presheaf_def by blast

lemma hom_act_fun_map:
  assumes C: "category C" and ls: "locally_small C" and \<phi>: "\<phi> \<in> Hom (PSh C) X Y"
  shows "psh_map C (elts_fun C X) (pre_fun C X) (elts_fun C Y) (pre_fun C Y) (act_fun C \<phi>)"
proof -
  have \<phi>P: "\<phi> \<in> PArr C"
    using \<phi> by simp
  have s: "asrc \<phi> = X" and t: "atgt \<phi> = Y"
    using \<phi> \<phi>P by simp_all
  have \<phi>A: "\<phi> \<in> Arr (PSh C)"
    using \<phi>P by simp
  show ?thesis
    using arrow_is_psh_map[OF C ls \<phi>A] unfolding s t .
qed

text \<open>Being a presheaf, and being small, pass along an isomorphism.\<close>

theorem psh_iso_presheaf:
  assumes "category C" and "presheaf C Q R" and "psh_iso C Q R Q' R'"
  shows "presheaf C Q' R'"
proof -
  note C = assms(1) and P = assms(2)
  obtain \<mu> \<nu> where inv: "psh_inverse C Q R Q' R' \<mu> \<nu>"
    using assms(3) unfolding psh_iso_iff by blast
  note \<mu> = psh_inverse_map1[OF inv] and \<nu> = psh_inverse_map2[OF inv]
  have key: "R' \<cdot> \<langle>u, x\<rangle> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>\<rangle>"
    if u: "u \<in> Arr C" and x: "x \<in> Q' \<cdot> tgt\<^bsub>C\<^esub> u" for u x
  proof -
    have tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C"
      using C u by simp
    have nx: "\<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle> \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u"
      by (rule psh_map_val[OF \<nu> tu x])
    have "R' \<cdot> \<langle>u, x\<rangle> = R' \<cdot> \<langle>u, \<mu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>\<rangle>"
      unfolding psh_inverse_inv2[OF inv tu x] by (rule refl)
    also have "\<dots> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle>\<rangle>"
      by (rule psh_map_nat[OF \<mu> u nx, symmetric])
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule presheafI)
    fix u x
    assume u: "u \<in> Arr C" and x: "x \<in> Q' \<cdot> tgt\<^bsub>C\<^esub> u"
    have su: "src\<^bsub>C\<^esub> u \<in> Ob C" and tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C"
      using C u by simp_all
    have r: "R \<cdot> \<langle>u, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, x\<rangle>\<rangle> \<in> Q \<cdot> src\<^bsub>C\<^esub> u"
      by (rule presheaf_restr[OF P u psh_map_val[OF \<nu> tu x]])
    show "R' \<cdot> \<langle>u, x\<rangle> \<in> Q' \<cdot> src\<^bsub>C\<^esub> u"
      unfolding key[OF u x] by (rule psh_map_val[OF \<mu> su r])
  next
    fix c x
    assume c: "c \<in> Ob C" and x: "x \<in> Q' \<cdot> c"
    have i: "id\<^bsub>C\<^esub> c \<in> Arr C" "src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c) = c" "tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c) = c"
      using C c by simp_all
    have x': "x \<in> Q' \<cdot> tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> c)"
      using x i(3) by simp
    have "R' \<cdot> \<langle>id\<^bsub>C\<^esub> c, x\<rangle> = \<mu> \<cdot> \<langle>c, R \<cdot> \<langle>id\<^bsub>C\<^esub> c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
      using key[OF i(1) x'] unfolding i(2,3) .
    also have "\<dots> = \<mu> \<cdot> \<langle>c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle>"
      unfolding presheaf_id[OF P c psh_map_val[OF \<nu> c x]] by (rule refl)
    also have "\<dots> = x"
      by (rule psh_inverse_inv2[OF inv c x])
    finally show "R' \<cdot> \<langle>id\<^bsub>C\<^esub> c, x\<rangle> = x" .
  next
    fix u v x
    assume u: "u \<in> Arr C" and v: "v \<in> Arr C" and vu: "src\<^bsub>C\<^esub> v = tgt\<^bsub>C\<^esub> u"
      and x: "x \<in> Q' \<cdot> tgt\<^bsub>C\<^esub> v"
    have tv: "tgt\<^bsub>C\<^esub> v \<in> Ob C"
      using C v by simp
    have nx: "\<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> v, x\<rangle> \<in> Q \<cdot> tgt\<^bsub>C\<^esub> v"
      by (rule psh_map_val[OF \<nu> tv x])
    have y: "R \<cdot> \<langle>v, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> v, x\<rangle>\<rangle> \<in> Q \<cdot> tgt\<^bsub>C\<^esub> u"
      using presheaf_restr[OF P v nx] vu by simp
    have c: "v \<circ>\<^bsub>C\<^esub> u \<in> Arr C" "src\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u) = src\<^bsub>C\<^esub> u"
      "tgt\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u) = tgt\<^bsub>C\<^esub> v"
      using C u v vu by simp_all
    have x': "x \<in> Q' \<cdot> tgt\<^bsub>C\<^esub> (v \<circ>\<^bsub>C\<^esub> u)"
      using x c(3) by simp
    have "R' \<cdot> \<langle>v \<circ>\<^bsub>C\<^esub> u, x\<rangle> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>v \<circ>\<^bsub>C\<^esub> u, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> v, x\<rangle>\<rangle>\<rangle>"
      using key[OF c(1) x'] unfolding c(2,3) .
    also have "\<dots> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, R \<cdot> \<langle>v, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> v, x\<rangle>\<rangle>\<rangle>\<rangle>"
      unfolding presheaf_comp[OF P u v vu nx] by (rule refl)
    also have "\<dots> = R' \<cdot> \<langle>u, \<mu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, R \<cdot> \<langle>v, \<nu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> v, x\<rangle>\<rangle>\<rangle>\<rangle>"
      by (rule psh_map_nat[OF \<mu> u y])
    also have "\<dots> = R' \<cdot> \<langle>u, R' \<cdot> \<langle>v, x\<rangle>\<rangle>"
      unfolding key[OF v x] vu by (rule refl)
    finally show "R' \<cdot> \<langle>v \<circ>\<^bsub>C\<^esub> u, x\<rangle> = R' \<cdot> \<langle>u, R' \<cdot> \<langle>v, x\<rangle>\<rangle>" .
  qed
qed

theorem small_presheaf_iso:
  assumes "category C" and "small_presheaf C Q R" and "psh_iso C Q R Q' R'"
  shows "small_presheaf C Q' R'"
proof -
  note C = assms(1)
  obtain X l where X: "X \<in> DOb C" and lim: "colimiting C X Q R l"
    using assms(2) unfolding small_presheaf_def by blast
  obtain \<mu> \<nu> where inv: "psh_inverse C Q R Q' R' \<mu> \<nu>"
    using assms(3) unfolding psh_iso_iff by blast
  note \<mu> = psh_inverse_map1[OF inv] and \<nu> = psh_inverse_map2[OF inv]
  have pQ: "presheaf C Q R"
    by (rule colimiting_presheaf[OF lim])
  have cQ: "cocone C X Q R l"
    by (rule colimiting_cocone[OF lim])
  have pQ': "presheaf C Q' R'"
    by (rule psh_iso_presheaf[OF C pQ assms(3)])
  define l' where "l' = (\<lambda>v\<in>\<V>. \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> (psnd v), l \<cdot> v\<rangle>)"
  have l'_app: "l' \<cdot> \<langle>j, f\<rangle> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> f, l \<cdot> \<langle>j, f\<rangle>\<rangle>" if "M j" and "M f" for j f
  proof -
    have d: "dcls (\<lambda>v. \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> (psnd v), l \<cdot> v\<rangle>)"
      by dfn
    have "l' \<cdot> \<langle>j, f\<rangle> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> (psnd \<langle>j, f\<rangle>), l \<cdot> \<langle>j, f\<rangle>\<rangle>"
      unfolding l'_def by (rule app_Lam[OF d]) simp_all
    then show ?thesis
      using that by simp
  qed
  have l'_hom: "l' \<cdot> \<langle>j, f\<rangle> = \<mu> \<cdot> \<langle>c, l \<cdot> \<langle>j, f\<rangle>\<rangle>"
    if j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)" for c j f
  proof -
    have "src\<^bsub>C\<^esub> f = c"
      using f by simp
    then show ?thesis
      using l'_app[OF mem_M[OF j] mem_M[OF f]] by simp
  qed
  have m\<mu>: "mediates C X l l' \<mu>"
  proof (rule mediatesI)
    fix c j f
    assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
    show "\<mu> \<cdot> \<langle>c, l \<cdot> \<langle>j, f\<rangle>\<rangle> = l' \<cdot> \<langle>j, f\<rangle>"
      by (rule l'_hom[OF j f, symmetric])
  qed
  have cQ': "cocone C X Q' R' l'"
  proof (rule coconeI)
    fix c j f
    assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
    show "l' \<cdot> \<langle>j, f\<rangle> \<in> Q' \<cdot> c"
      unfolding l'_hom[OF j f] by (rule psh_map_val[OF \<mu> c cocone_val[OF cQ c j f]])
  next
    fix u j f
    assume u: "u \<in> Arr C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C (tgt\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j)"
    have tu: "tgt\<^bsub>C\<^esub> u \<in> Ob C"
      using C u by simp
    have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = tgt\<^bsub>C\<^esub> u" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o j"
      using f by simp_all
    have fu: "f \<circ>\<^bsub>C\<^esub> u \<in> Hom C (src\<^bsub>C\<^esub> u) (dg X \<cdot>\<^sub>o j)"
      using C u fa by simp
    have "l' \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, l \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle>\<rangle>"
      by (rule l'_hom[OF j fu])
    also have "\<dots> = \<mu> \<cdot> \<langle>src\<^bsub>C\<^esub> u, R \<cdot> \<langle>u, l \<cdot> \<langle>j, f\<rangle>\<rangle>\<rangle>"
      unfolding cocone_nat[OF cQ u j f] by (rule refl)
    also have "\<dots> = R' \<cdot> \<langle>u, \<mu> \<cdot> \<langle>tgt\<^bsub>C\<^esub> u, l \<cdot> \<langle>j, f\<rangle>\<rangle>\<rangle>"
      by (rule psh_map_nat[OF \<mu> u cocone_val[OF cQ tu j f]])
    also have "\<dots> = R' \<cdot> \<langle>u, l' \<cdot> \<langle>j, f\<rangle>\<rangle>"
      unfolding l'_hom[OF j f] by (rule refl)
    finally show "l' \<cdot> \<langle>j, f \<circ>\<^bsub>C\<^esub> u\<rangle> = R' \<cdot> \<langle>u, l' \<cdot> \<langle>j, f\<rangle>\<rangle>" .
  next
    fix c b f
    assume c: "c \<in> Ob C" and b: "b \<in> Arr (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b)"
    have cX: "category (ix X)"
      using X by simp
    have s: "src\<^bsub>ix X\<^esub> b \<in> Ob (ix X)" and t: "tgt\<^bsub>ix X\<^esub> b \<in> Ob (ix X)"
      using cX b by simp_all
    have fa: "f \<in> Arr C" "src\<^bsub>C\<^esub> f = c" "tgt\<^bsub>C\<^esub> f = dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b"
      using f by simp_all
    have Fb: "dg X \<cdot>\<^sub>a b \<in> Arr C" "src\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>a b) = dg X \<cdot>\<^sub>o src\<^bsub>ix X\<^esub> b"
      "tgt\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>a b) = dg X \<cdot>\<^sub>o tgt\<^bsub>ix X\<^esub> b"
      using X b by simp_all
    have Fbf: "dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f \<in> Hom C c (dg X \<cdot>\<^sub>o tgt\<^bsub>ix X\<^esub> b)"
      using C Fb fa by simp
    show "l' \<cdot> \<langle>tgt\<^bsub>ix X\<^esub> b, dg X \<cdot>\<^sub>a b \<circ>\<^bsub>C\<^esub> f\<rangle> = l' \<cdot> \<langle>src\<^bsub>ix X\<^esub> b, f\<rangle>"
      unfolding l'_hom[OF t Fbf] l'_hom[OF s f] cocone_compat[OF cQ c b f] by (rule refl)
  qed
  have lim': "colimiting C X Q' R' l'"
  proof (rule colimitingI[OF pQ' cQ'])
    fix Q'' R'' l''
    assume p'': "presheaf C Q'' R''" and c'': "cocone C X Q'' R'' l''"
    obtain m where m: "psh_map C Q R Q'' R'' m" and mm: "mediates C X l l'' m"
      using colimiting_ex[OF lim p'' c''] by blast
    have med: "mediates C X l' l'' (\<lambda>p\<in>\<V>. m \<cdot> \<langle>pfst p, \<nu> \<cdot> p\<rangle>)"
    proof (rule mediatesI)
      fix c j f
      assume c: "c \<in> Ob C" and j: "j \<in> Ob (ix X)" and f: "f \<in> Hom C c (dg X \<cdot>\<^sub>o j)"
      have lv: "l \<cdot> \<langle>j, f\<rangle> \<in> Q \<cdot> c"
        by (rule cocone_val[OF cQ c j f])
      show "(\<lambda>p\<in>\<V>. m \<cdot> \<langle>pfst p, \<nu> \<cdot> p\<rangle>) \<cdot> \<langle>c, l' \<cdot> \<langle>j, f\<rangle>\<rangle> = l'' \<cdot> \<langle>j, f\<rangle>"
        unfolding app_comp_Lam[OF mem_M[OF c] M_app] l'_hom[OF j f] psh_inverse_inv1[OF inv c lv]
          mediatesD[OF mm c j f]
        by (rule refl)
    qed
    show "\<exists>\<mu>. psh_map C Q' R' Q'' R'' \<mu> \<and> mediates C X l' l'' \<mu>"
      using psh_map_comp[OF C \<nu> m] med by blast
  next
    fix Q'' R'' l'' m1 m2
    assume p'': "presheaf C Q'' R''" and c'': "cocone C X Q'' R'' l''"
      and m1: "psh_map C Q' R' Q'' R'' m1" and e1: "mediates C X l' l'' m1"
      and m2: "psh_map C Q' R' Q'' R'' m2" and e2: "mediates C X l' l'' m2"
    have a: "psh_agree C Q (\<lambda>p\<in>\<V>. m1 \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>) (\<lambda>p\<in>\<V>. m2 \<cdot> \<langle>pfst p, \<mu> \<cdot> p\<rangle>)"
      by (rule colimiting_unique[OF lim p'' c'' psh_map_comp[OF C \<mu> m1] mediates_comp[OF m\<mu> e1]
            psh_map_comp[OF C \<mu> m2] mediates_comp[OF m\<mu> e2]])
    show "psh_agree C Q' m1 m2"
    proof (rule psh_agreeI)
      fix c x
      assume c: "c \<in> Ob C" and x: "x \<in> Q' \<cdot> c"
      have nx: "\<nu> \<cdot> \<langle>c, x\<rangle> \<in> Q \<cdot> c"
        by (rule psh_map_val[OF \<nu> c x])
      have "m1 \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle> = m2 \<cdot> \<langle>c, \<mu> \<cdot> \<langle>c, \<nu> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
        using psh_agreeD[OF a c nx] unfolding app_comp_Lam[OF mem_M[OF c] mem_M[OF nx]] .
      then show "m1 \<cdot> \<langle>c, x\<rangle> = m2 \<cdot> \<langle>c, x\<rangle>"
        unfolding psh_inverse_inv2[OF inv c x] .
    qed
  qed
  show ?thesis
    unfolding small_presheaf_def using X lim' by blast
qed

text \<open>Every small presheaf is presented by an object of \<open>PSh C\<close>.\<close>

corollary small_presheaf_presented:
  assumes "category C" and "locally_small C" and "small_presheaf C Q R"
  shows "\<exists>\<^sub>s X. X \<in> DOb C \<and> (\<exists>\<alpha> \<alpha>'. psh_inverse C (elts_fun C X) (pre_fun C X) Q R \<alpha> \<alpha>')"
  using small_presheaf_is_diagram_presheaf[OF assms] unfolding psh_iso_iff by blast

text \<open>
  Let \<open>X\<close> present \<open>(Q, R)\<close> by \<open>\<alpha>\<close> and \<open>Y\<close> present \<open>(Q', R')\<close> by \<open>\<beta>\<close>. Every map
  \<open>\<eta> : (Q, R) \<rightarrow> (Q', R')\<close> makes the square commute with exactly one arrow \<open>X \<rightarrow> Y\<close>. Every arrow
  \<open>X \<rightarrow> Y\<close> makes the square commute with some map \<open>\<eta>\<close>, and two such maps have the same
  components.
\<close>

theorem small_psh_map_is_arrow:
  assumes "category C" and "locally_small C" and "X \<in> DOb C" and "Y \<in> DOb C"
    and "psh_inverse C (elts_fun C X) (pre_fun C X) Q R \<alpha> \<alpha>'"
    and "psh_inverse C (elts_fun C Y) (pre_fun C Y) Q' R' \<beta> \<beta>'"
    and "psh_map C Q R Q' R' \<eta>"
  shows "\<exists>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi> \<and>
      (\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta> \<phi>' \<longrightarrow> \<phi>' = \<phi>)"
proof -
  note C = assms(1) and ls = assms(2) and X = assms(3) and Y = assms(4)
    and in\<alpha> = assms(5) and in\<beta> = assms(6) and \<eta> = assms(7)
  note \<alpha> = psh_inverse_map1[OF in\<alpha>] and \<beta>' = psh_inverse_map2[OF in\<beta>]
  define g where "g = (\<lambda>p\<in>\<V>. \<eta> \<cdot> \<langle>pfst p, \<alpha> \<cdot> p\<rangle>)"
  define k where "k = (\<lambda>p\<in>\<V>. \<beta>' \<cdot> \<langle>pfst p, g \<cdot> p\<rangle>)"
  have g: "psh_map C (elts_fun C X) (pre_fun C X) Q' R' g"
    unfolding g_def by (rule psh_map_comp[OF C \<alpha> \<eta>])
  have k: "psh_map C (elts_fun C X) (pre_fun C X) (elts_fun C Y) (pre_fun C Y) k"
    unfolding k_def by (rule psh_map_comp[OF C g \<beta>'])
  have k_app: "k \<cdot> \<langle>c, x\<rangle> = \<beta>' \<cdot> \<langle>c, \<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>" if "M c" and "M x" for c x
    unfolding k_def g_def app_comp_Lam[OF that] by (rule refl)
  obtain \<phi> where "M \<phi>" and hom: "\<phi> \<in> Hom (PSh C) X Y"
    and ag: "psh_agree C (elts_fun C X) k (act_fun C \<phi>)"
    and uniq: "\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_agree C (elts_fun C X) k (act_fun C \<phi>') \<longrightarrow> \<phi>' = \<phi>"
    using psh_map_is_arrow[OF C ls X Y k] by blast
  have sq: "psh_square C X \<alpha> \<beta> \<eta> \<phi>"
  proof (rule psh_squareI)
    fix c x
    assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
    have ex: "\<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> \<in> Q' \<cdot> c"
      by (rule psh_map_val[OF \<eta> c psh_map_val[OF \<alpha> c x]])
    have "\<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<beta> \<cdot> \<langle>c, \<beta>' \<cdot> \<langle>c, \<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>\<rangle>"
      by (rule psh_inverse_inv2[OF in\<beta> c ex, symmetric])
    also have "\<dots> = \<beta> \<cdot> \<langle>c, k \<cdot> \<langle>c, x\<rangle>\<rangle>"
      unfolding k_app[OF mem_M[OF c] mem_M[OF x]] by (rule refl)
    also have "\<dots> = \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>"
      unfolding psh_agreeD[OF ag c x] by (rule refl)
    finally show "\<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>" .
  qed
  have un: "\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta> \<phi>' \<longrightarrow> \<phi>' = \<phi>"
  proof (intro allI impI)
    fix \<phi>'
    assume "M \<phi>'" and h': "\<phi>' \<in> Hom (PSh C) X Y" and sq': "psh_square C X \<alpha> \<beta> \<eta> \<phi>'"
    have ag': "psh_agree C (elts_fun C X) k (act_fun C \<phi>')"
    proof (rule psh_agreeI)
      fix c x
      assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
      have ax: "act_fun C \<phi>' \<cdot> \<langle>c, x\<rangle> \<in> elts_fun C Y \<cdot> c"
        by (rule psh_map_val[OF hom_act_fun_map[OF C ls h'] c x])
      have "k \<cdot> \<langle>c, x\<rangle> = \<beta>' \<cdot> \<langle>c, \<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
        by (rule k_app[OF mem_M[OF c] mem_M[OF x]])
      also have "\<dots> = \<beta>' \<cdot> \<langle>c, \<beta> \<cdot> \<langle>c, act_fun C \<phi>' \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
        unfolding psh_squareD[OF sq' c x] by (rule refl)
      also have "\<dots> = act_fun C \<phi>' \<cdot> \<langle>c, x\<rangle>"
        by (rule psh_inverse_inv1[OF in\<beta> c ax])
      finally show "k \<cdot> \<langle>c, x\<rangle> = act_fun C \<phi>' \<cdot> \<langle>c, x\<rangle>" .
    qed
    show "\<phi>' = \<phi>"
      using uniq \<open>M \<phi>'\<close> h' ag' by blast
  qed
  show ?thesis
    using \<open>M \<phi>\<close> hom sq un by blast
qed

theorem arrow_is_small_psh_map:
  assumes "category C" and "locally_small C" and "X \<in> DOb C" and "Y \<in> DOb C"
    and "psh_inverse C (elts_fun C X) (pre_fun C X) Q R \<alpha> \<alpha>'"
    and "psh_inverse C (elts_fun C Y) (pre_fun C Y) Q' R' \<beta> \<beta>'"
    and "\<phi> \<in> Hom (PSh C) X Y"
  shows "\<exists>\<eta>. psh_map C Q R Q' R' \<eta> \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi>"
    and "\<forall>\<eta> \<eta>'. psh_square C X \<alpha> \<beta> \<eta> \<phi> \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta>' \<phi> \<longrightarrow> psh_agree C Q \<eta> \<eta>'"
proof -
  note C = assms(1) and ls = assms(2) and X = assms(3) and Y = assms(4)
    and in\<alpha> = assms(5) and in\<beta> = assms(6) and \<phi> = assms(7)
  note \<alpha>' = psh_inverse_map2[OF in\<alpha>] and \<beta> = psh_inverse_map1[OF in\<beta>]
  define a where "a = (\<lambda>p\<in>\<V>. act_fun C \<phi> \<cdot> \<langle>pfst p, \<alpha>' \<cdot> p\<rangle>)"
  define e where "e = (\<lambda>p\<in>\<V>. \<beta> \<cdot> \<langle>pfst p, a \<cdot> p\<rangle>)"
  have a: "psh_map C Q R (elts_fun C Y) (pre_fun C Y) a"
    unfolding a_def by (rule psh_map_comp[OF C \<alpha>' hom_act_fun_map[OF C ls \<phi>]])
  have e: "psh_map C Q R Q' R' e"
    unfolding e_def by (rule psh_map_comp[OF C a \<beta>])
  have e_app: "e \<cdot> \<langle>c, x\<rangle> = \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, \<alpha>' \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>" if "M c" and "M x" for c x
    unfolding e_def a_def app_comp_Lam[OF that] by (rule refl)
  have sq: "psh_square C X \<alpha> \<beta> e \<phi>"
  proof (rule psh_squareI)
    fix c x
    assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
    show "e \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>"
      unfolding e_app[OF mem_M[OF c] M_app] psh_inverse_inv1[OF in\<alpha> c x] by (rule refl)
  qed
  show "\<exists>\<eta>. psh_map C Q R Q' R' \<eta> \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi>"
    using e sq by blast
  show "\<forall>\<eta> \<eta>'. psh_square C X \<alpha> \<beta> \<eta> \<phi> \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta>' \<phi> \<longrightarrow> psh_agree C Q \<eta> \<eta>'"
  proof (intro allI impI)
    fix \<eta> \<eta>'
    assume s1: "psh_square C X \<alpha> \<beta> \<eta> \<phi>" and s2: "psh_square C X \<alpha> \<beta> \<eta>' \<phi>"
    show "psh_agree C Q \<eta> \<eta>'"
    proof (rule psh_agreeI)
      fix c x
      assume c: "c \<in> Ob C" and x: "x \<in> Q \<cdot> c"
      have x': "\<alpha>' \<cdot> \<langle>c, x\<rangle> \<in> elts_fun C X \<cdot> c"
        by (rule psh_map_val[OF \<alpha>' c x])
      have "\<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, \<alpha>' \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle> = \<eta>' \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, \<alpha>' \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
        unfolding psh_squareD[OF s1 c x'] psh_squareD[OF s2 c x'] by (rule refl)
      then show "\<eta> \<cdot> \<langle>c, x\<rangle> = \<eta>' \<cdot> \<langle>c, x\<rangle>"
        unfolding psh_inverse_inv2[OF in\<alpha> c x] .
    qed
  qed
qed

text \<open>
  The correspondence respects identities and composition: the identity map goes with the identity
  arrow, and the composite of two maps goes with the composite of their arrows.
\<close>

theorem psh_square_id:
  assumes "category C" and "locally_small C" and "X \<in> DOb C"
  shows "psh_square C X \<alpha> \<alpha> (\<lambda>p\<in>\<V>. psnd p) (id\<^bsub>PSh C\<^esub> X)"
proof (rule psh_squareI)
  note C = assms(1) and ls = assms(2) and X = assms(3)
  fix c x
  assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
  have x': "x \<in> elts C X c"
    using x elts_fun_app[OF C ls X c] by simp
  have IP: "id\<^bsub>PSh C\<^esub> X \<in> PArr C"
    using C ls X by simp
  have s: "asrc (id\<^bsub>PSh C\<^esub> X) = X"
    using X mem_M[OF X] by simp
  have x'': "x \<in> elts C (asrc (id\<^bsub>PSh C\<^esub> X)) c"
    using x' s by simp
  have "act_fun C (id\<^bsub>PSh C\<^esub> X) \<cdot> \<langle>c, x\<rangle> = act C (id\<^bsub>PSh C\<^esub> X) c x"
    by (rule act_fun_app[OF C ls IP c x''])
  also have "\<dots> = x"
    by (rule act_functorial(1)[OF C ls, rule_format, OF mem_M[OF X] mem_M[OF c] mem_M[OF x'] X c x'])
  finally have a: "act_fun C (id\<^bsub>PSh C\<^esub> X) \<cdot> \<langle>c, x\<rangle> = x" .
  show "(\<lambda>p\<in>\<V>. psnd p) \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<alpha> \<cdot> \<langle>c, act_fun C (id\<^bsub>PSh C\<^esub> X) \<cdot> \<langle>c, x\<rangle>\<rangle>"
    unfolding app_id_Lam[OF mem_M[OF c] M_app] a by (rule refl)
qed

theorem psh_square_comp:
  assumes "category C" and "locally_small C"
    and "\<phi> \<in> Hom (PSh C) X Y" and "\<psi> \<in> Hom (PSh C) Y Z"
    and "psh_square C X \<alpha> \<beta> \<eta> \<phi>" and "psh_square C Y \<beta> \<gamma> \<theta> \<psi>"
  shows "psh_square C X \<alpha> \<gamma> (\<lambda>p\<in>\<V>. \<theta> \<cdot> \<langle>pfst p, \<eta> \<cdot> p\<rangle>) (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>)"
proof -
  note C = assms(1) and ls = assms(2) and \<phi> = assms(3) and \<psi> = assms(4)
    and s1 = assms(5) and s2 = assms(6)
  have \<phi>P: "\<phi> \<in> PArr C" and \<psi>P: "\<psi> \<in> PArr C"
    using \<phi> \<psi> by simp_all
  have s\<phi>: "asrc \<phi> = X" "atgt \<phi> = Y"
    using \<phi> \<phi>P by simp_all
  have s\<psi>: "asrc \<psi> = Y" "atgt \<psi> = Z"
    using \<psi> \<psi>P by simp_all
  have X: "X \<in> DOb C"
    using PArr_asrc[OF \<phi>P] s\<phi> by simp
  have \<phi>A: "\<phi> \<in> Arr (PSh C)" and \<psi>A: "\<psi> \<in> Arr (PSh C)"
    using \<phi>P \<psi>P by simp_all
  have st: "src\<^bsub>PSh C\<^esub> \<psi> = tgt\<^bsub>PSh C\<^esub> \<phi>"
    using \<phi>P \<psi>P s\<phi> s\<psi> by simp
  have cP: "\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi> \<in> PArr C"
    using C ls \<phi>P \<psi>P s\<phi> s\<psi> by simp
  have cs: "asrc (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) = X"
    using \<phi>P \<psi>P s\<phi> by simp
  show ?thesis
  proof (rule psh_squareI)
    fix c x
    assume c: "c \<in> Ob C" and x: "x \<in> elts_fun C X \<cdot> c"
    have x': "x \<in> elts C (asrc \<phi>) c"
      using x elts_fun_app[OF C ls X c] s\<phi> by simp
    have x'': "x \<in> elts C (asrc (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>)) c"
      using x' s\<phi> cs by simp
    have ax: "act_fun C \<phi> \<cdot> \<langle>c, x\<rangle> \<in> elts_fun C Y \<cdot> c"
      by (rule psh_map_val[OF hom_act_fun_map[OF C ls \<phi>] c x])
    have ax': "act C \<phi> c x \<in> elts C (asrc \<psi>) c"
      using act_elts[OF C ls \<phi>P x'] s\<phi> s\<psi> by simp
    have "act_fun C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) \<cdot> \<langle>c, x\<rangle> = act C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) c x"
      by (rule act_fun_app[OF C ls cP c x''])
    also have "\<dots> = act C \<psi> c (act C \<phi> c x)"
      by (rule act_functorial(2)[OF C ls, rule_format,
            OF mem_M[OF \<phi>A] mem_M[OF \<psi>A] mem_M[OF c] mem_M[OF x'] \<phi>A \<psi>A st c x'])
    also have "\<dots> = act_fun C \<psi> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>"
      unfolding act_fun_app[OF C ls \<phi>P c x'] act_fun_app[OF C ls \<psi>P c ax'] by (rule refl)
    finally have comp: "act_fun C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) \<cdot> \<langle>c, x\<rangle> =
        act_fun C \<psi> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>" .
    have "(\<lambda>p\<in>\<V>. \<theta> \<cdot> \<langle>pfst p, \<eta> \<cdot> p\<rangle>) \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> = \<theta> \<cdot> \<langle>c, \<eta> \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
      by (rule app_comp_Lam[OF mem_M[OF c] M_app])
    also have "\<dots> = \<theta> \<cdot> \<langle>c, \<beta> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
      unfolding psh_squareD[OF s1 c x] by (rule refl)
    also have "\<dots> = \<gamma> \<cdot> \<langle>c, act_fun C \<psi> \<cdot> \<langle>c, act_fun C \<phi> \<cdot> \<langle>c, x\<rangle>\<rangle>\<rangle>"
      by (rule psh_squareD[OF s2 c ax])
    also have "\<dots> = \<gamma> \<cdot> \<langle>c, act_fun C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) \<cdot> \<langle>c, x\<rangle>\<rangle>"
      unfolding comp by (rule refl)
    finally show "(\<lambda>p\<in>\<V>. \<theta> \<cdot> \<langle>pfst p, \<eta> \<cdot> p\<rangle>) \<cdot> \<langle>c, \<alpha> \<cdot> \<langle>c, x\<rangle>\<rangle> =
        \<gamma> \<cdot> \<langle>c, act_fun C (\<psi> \<circ>\<^bsub>PSh C\<^esub> \<phi>) \<cdot> \<langle>c, x\<rangle>\<rangle>" .
  qed
qed

text \<open>
  \<open>small_presheaf_presented\<close>, \<open>small_psh_map_is_arrow\<close> and \<open>arrow_is_small_psh_map\<close> in one
  statement, for two given small presheaves: the maps between them, up to having the same
  components, are the arrows of \<open>PSh C\<close> between two objects that present them.
\<close>

corollary small_presheaf_hom:
  assumes "category C" and "locally_small C"
    and "small_presheaf C Q R" and "small_presheaf C Q' R'"
  shows "\<exists>\<^sub>s X Y. X \<in> DOb C \<and> Y \<in> DOb C \<and> (\<exists>\<alpha> \<alpha>' \<beta> \<beta>'.
      psh_inverse C (elts_fun C X) (pre_fun C X) Q R \<alpha> \<alpha>' \<and>
      psh_inverse C (elts_fun C Y) (pre_fun C Y) Q' R' \<beta> \<beta>' \<and>
      (\<forall>\<eta>. psh_map C Q R Q' R' \<eta> \<longrightarrow>
        (\<exists>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi> \<and>
          (\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta> \<phi>' \<longrightarrow> \<phi>' = \<phi>))) \<and>
      (\<forall>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<longrightarrow>
        (\<exists>\<eta>. psh_map C Q R Q' R' \<eta> \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi>) \<and>
        (\<forall>\<eta> \<eta>'. psh_square C X \<alpha> \<beta> \<eta> \<phi> \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta>' \<phi> \<longrightarrow>
          psh_agree C Q \<eta> \<eta>')))"
proof -
  note C = assms(1) and ls = assms(2)
  obtain X \<alpha> \<alpha>' where "M X" and X: "X \<in> DOb C"
    and in\<alpha>: "psh_inverse C (elts_fun C X) (pre_fun C X) Q R \<alpha> \<alpha>'"
    using small_presheaf_presented[OF C ls assms(3)] by blast
  obtain Y \<beta> \<beta>' where "M Y" and Y: "Y \<in> DOb C"
    and in\<beta>: "psh_inverse C (elts_fun C Y) (pre_fun C Y) Q' R' \<beta> \<beta>'"
    using small_presheaf_presented[OF C ls assms(4)] by blast
  have P1: "\<forall>\<eta>. psh_map C Q R Q' R' \<eta> \<longrightarrow>
      (\<exists>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi> \<and>
        (\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta> \<phi>' \<longrightarrow> \<phi>' = \<phi>))"
  proof (intro allI impI)
    fix \<eta>
    assume \<eta>: "psh_map C Q R Q' R' \<eta>"
    show "\<exists>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi> \<and>
        (\<forall>\<^sub>s \<phi>'. \<phi>' \<in> Hom (PSh C) X Y \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta> \<phi>' \<longrightarrow> \<phi>' = \<phi>)"
      by (rule small_psh_map_is_arrow[OF C ls X Y in\<alpha> in\<beta> \<eta>])
  qed
  have P2: "\<forall>\<^sub>s \<phi>. \<phi> \<in> Hom (PSh C) X Y \<longrightarrow>
      (\<exists>\<eta>. psh_map C Q R Q' R' \<eta> \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi>) \<and>
      (\<forall>\<eta> \<eta>'. psh_square C X \<alpha> \<beta> \<eta> \<phi> \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta>' \<phi> \<longrightarrow> psh_agree C Q \<eta> \<eta>')"
  proof (intro allI impI)
    fix \<phi>
    assume "M \<phi>" and \<phi>: "\<phi> \<in> Hom (PSh C) X Y"
    show "(\<exists>\<eta>. psh_map C Q R Q' R' \<eta> \<and> psh_square C X \<alpha> \<beta> \<eta> \<phi>) \<and>
        (\<forall>\<eta> \<eta>'. psh_square C X \<alpha> \<beta> \<eta> \<phi> \<longrightarrow> psh_square C X \<alpha> \<beta> \<eta>' \<phi> \<longrightarrow> psh_agree C Q \<eta> \<eta>')"
      using arrow_is_small_psh_map[OF C ls X Y in\<alpha> in\<beta> \<phi>] by (rule conjI)
  qed
  show ?thesis
    using \<open>M X\<close> \<open>M Y\<close> X Y in\<alpha> in\<beta> P1 P2 by blast
qed

end
