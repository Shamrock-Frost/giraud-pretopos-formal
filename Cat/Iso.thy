section \<open>Isomorphisms\<close>

theory Iso
  imports Functor
begin

text \<open>
  General facts about isomorphisms: inverses are unique, identities and composites of
  isomorphisms are isomorphisms, functors preserve them.
\<close>

subsection \<open>Introducing and eliminating an isomorphism\<close>

text \<open>
  An isomorphism is an arrow with a two-sided inverse. The rules below state this with the
  inverse as an explicit arrow, so that no inverse operation is needed: a proof that uses an
  inverse obtains one by \<open>isoE\<close>.
\<close>

lemma isoI:
  assumes "f \<in> Arr C" and "g \<in> Arr C" and "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f" and "tgt\<^bsub>C\<^esub> g = src\<^bsub>C\<^esub> f"
    and "g \<circ>\<^bsub>C\<^esub> f = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)" and "f \<circ>\<^bsub>C\<^esub> g = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f)"
  shows "iso C f"
  unfolding iso_def using assms by (blast dest: mem_M)

lemma isoE:
  assumes "iso C f"
  obtains g where "g \<in> Arr C" and "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f" and "tgt\<^bsub>C\<^esub> g = src\<^bsub>C\<^esub> f"
    and "g \<circ>\<^bsub>C\<^esub> f = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)" and "f \<circ>\<^bsub>C\<^esub> g = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f)"
  using assms unfolding iso_def by blast

lemma iso_arr: "iso C f \<Longrightarrow> f \<in> Arr C"
  unfolding iso_def by blast

text \<open>
  The unit laws with the object named (proved in \<open>Functor\<close>), under the names used below and in
  \<open>Localization\<close>.
\<close>

lemmas cat_comp_id = cat_id_right_eq
lemmas cat_id_comp = cat_id_left_eq

text \<open>A left inverse and a right inverse of the same arrow are equal; so an inverse is unique.\<close>

lemma inverse_unique:
  assumes C: "category C" and f: "f \<in> Arr C" and g: "g \<in> Arr C" and h: "h \<in> Arr C"
    and gs: "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f" and hs: "src\<^bsub>C\<^esub> h = tgt\<^bsub>C\<^esub> f"
    and gt: "tgt\<^bsub>C\<^esub> g = src\<^bsub>C\<^esub> f" and ht: "tgt\<^bsub>C\<^esub> h = src\<^bsub>C\<^esub> f"
    and gf: "g \<circ>\<^bsub>C\<^esub> f = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)" and fh: "f \<circ>\<^bsub>C\<^esub> h = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f)"
  shows "g = h"
proof -
  have "g = g \<circ>\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> h)"
    using C g fh gs by simp
  also have "\<dots> = (g \<circ>\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> h"
    using C f g h gs ht by (simp add: cat_assoc)
  also have "\<dots> = h"
    using C h gf ht by simp
  finally show ?thesis .
qed

subsection \<open>Closure properties\<close>

lemma iso_id:
  assumes "category C" and "x \<in> Ob C"
  shows "iso C (id\<^bsub>C\<^esub> x)"
  by (rule isoI[where g = "id\<^bsub>C\<^esub> x"]) (use assms in simp_all)

lemma iso_inverse:
  assumes C: "category C" and f: "iso C f"
    and g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f" "tgt\<^bsub>C\<^esub> g = src\<^bsub>C\<^esub> f"
      "g \<circ>\<^bsub>C\<^esub> f = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)" "f \<circ>\<^bsub>C\<^esub> g = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f)"
  shows "iso C g"
  by (rule isoI[where g = f]) (use iso_arr[OF f] g in simp_all)

lemma iso_comp:
  assumes C: "category C" and f: "iso C f" and g: "iso C g" and gf: "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f"
  shows "iso C (g \<circ>\<^bsub>C\<^esub> f)"
proof -
  have fA: "f \<in> Arr C" and gA: "g \<in> Arr C"
    using f g by (simp_all add: iso_arr)
  obtain f' where f': "f' \<in> Arr C" "src\<^bsub>C\<^esub> f' = tgt\<^bsub>C\<^esub> f" "tgt\<^bsub>C\<^esub> f' = src\<^bsub>C\<^esub> f"
    "f' \<circ>\<^bsub>C\<^esub> f = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)" "f \<circ>\<^bsub>C\<^esub> f' = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f)"
    using f by (rule isoE)
  obtain g' where g': "g' \<in> Arr C" "src\<^bsub>C\<^esub> g' = tgt\<^bsub>C\<^esub> g" "tgt\<^bsub>C\<^esub> g' = src\<^bsub>C\<^esub> g"
    "g' \<circ>\<^bsub>C\<^esub> g = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> g)" "g \<circ>\<^bsub>C\<^esub> g' = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> g)"
    using g by (rule isoE)
  have l: "(f' \<circ>\<^bsub>C\<^esub> g') \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)"
  proof -
    have "(f' \<circ>\<^bsub>C\<^esub> g') \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = f' \<circ>\<^bsub>C\<^esub> (g' \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f))"
      by (rule cat_assoc[symmetric]) (use C fA gA f' g' gf in simp_all)
    also have "\<dots> = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)"
      using C fA gA f' g' gf cat_assoc[OF C fA gA g'(1) gf g'(2)] by simp
    finally show ?thesis .
  qed
  have r: "(g \<circ>\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> (f' \<circ>\<^bsub>C\<^esub> g') = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f))"
  proof -
    have "(g \<circ>\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> (f' \<circ>\<^bsub>C\<^esub> g') = g \<circ>\<^bsub>C\<^esub> (f \<circ>\<^bsub>C\<^esub> (f' \<circ>\<^bsub>C\<^esub> g'))"
      by (rule cat_assoc[symmetric]) (use C fA gA f' g' gf in simp_all)
    also have "\<dots> = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f))"
      using C fA gA f' g' gf cat_assoc[OF C g'(1) f'(1) fA] by simp
    finally show ?thesis .
  qed
  show ?thesis
    by (rule isoI[where g = "f' \<circ>\<^bsub>C\<^esub> g'"]) (use C fA gA f' g' gf l r in simp_all)
qed

text \<open>If \<open>g \<circ> f\<close> and \<open>g\<close> are isomorphisms, so is \<open>f\<close>.\<close>

lemma iso_right_factor:
  assumes C: "category C" and f: "f \<in> Arr C" and g: "iso C g" and gf: "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f"
    and h: "iso C (g \<circ>\<^bsub>C\<^esub> f)"
  shows "iso C f"
proof -
  have gA: "g \<in> Arr C"
    using g by (rule iso_arr)
  obtain g' where g': "g' \<in> Arr C" "src\<^bsub>C\<^esub> g' = tgt\<^bsub>C\<^esub> g" "tgt\<^bsub>C\<^esub> g' = src\<^bsub>C\<^esub> g"
    "g' \<circ>\<^bsub>C\<^esub> g = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> g)" "g \<circ>\<^bsub>C\<^esub> g' = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> g)"
    using g by (rule isoE)
  have "iso C g'"
    using C g g' by (rule iso_inverse)
  then have "iso C (g' \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f))"
    using C h gA f gf g' by (simp add: iso_comp)
  moreover have "g' \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = f"
    using C gA f gf g' by (simp add: cat_assoc)
  ultimately show ?thesis
    by simp
qed

subsection \<open>Cancellation\<close>

lemma iso_cancel_right:
  assumes C: "category C" and w: "iso C w" and a: "a \<in> Arr C" and b: "b \<in> Arr C"
    and as: "src\<^bsub>C\<^esub> a = tgt\<^bsub>C\<^esub> w" and bs: "src\<^bsub>C\<^esub> b = tgt\<^bsub>C\<^esub> w"
    and eq: "a \<circ>\<^bsub>C\<^esub> w = b \<circ>\<^bsub>C\<^esub> w"
  shows "a = b"
proof -
  have wA: "w \<in> Arr C"
    using w by (rule iso_arr)
  obtain w' where w': "w' \<in> Arr C" "src\<^bsub>C\<^esub> w' = tgt\<^bsub>C\<^esub> w" "tgt\<^bsub>C\<^esub> w' = src\<^bsub>C\<^esub> w"
    "w' \<circ>\<^bsub>C\<^esub> w = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> w)" "w \<circ>\<^bsub>C\<^esub> w' = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> w)"
    using w by (rule isoE)
  have "a = (a \<circ>\<^bsub>C\<^esub> w) \<circ>\<^bsub>C\<^esub> w'"
    using C a wA w' as by (simp add: cat_assoc[symmetric])
  also have "\<dots> = (b \<circ>\<^bsub>C\<^esub> w) \<circ>\<^bsub>C\<^esub> w'"
    by (simp add: eq)
  also have "\<dots> = b"
    using C b wA w' bs by (simp add: cat_assoc[symmetric])
  finally show ?thesis .
qed

lemma iso_cancel_left:
  assumes C: "category C" and w: "iso C w" and a: "a \<in> Arr C" and b: "b \<in> Arr C"
    and at: "tgt\<^bsub>C\<^esub> a = src\<^bsub>C\<^esub> w" and bt: "tgt\<^bsub>C\<^esub> b = src\<^bsub>C\<^esub> w"
    and eq: "w \<circ>\<^bsub>C\<^esub> a = w \<circ>\<^bsub>C\<^esub> b"
  shows "a = b"
proof -
  have wA: "w \<in> Arr C"
    using w by (rule iso_arr)
  obtain w' where w': "w' \<in> Arr C" "src\<^bsub>C\<^esub> w' = tgt\<^bsub>C\<^esub> w" "tgt\<^bsub>C\<^esub> w' = src\<^bsub>C\<^esub> w"
    "w' \<circ>\<^bsub>C\<^esub> w = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> w)" "w \<circ>\<^bsub>C\<^esub> w' = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> w)"
    using w by (rule isoE)
  have "a = w' \<circ>\<^bsub>C\<^esub> (w \<circ>\<^bsub>C\<^esub> a)"
    using C a wA w' at by (simp add: cat_assoc)
  also have "\<dots> = w' \<circ>\<^bsub>C\<^esub> (w \<circ>\<^bsub>C\<^esub> b)"
    by (simp add: eq)
  also have "\<dots> = b"
    using C b wA w' bt by (simp add: cat_assoc)
  finally show ?thesis .
qed

subsection \<open>Functors preserve isomorphisms\<close>

lemma functor_iso:
  assumes C: "category C" and F: "is_functor F C D" and f: "iso C f"
  shows "iso D (F \<cdot>\<^sub>a f)"
proof -
  have fA: "f \<in> Arr C"
    using f by (rule iso_arr)
  obtain g where g: "g \<in> Arr C" "src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f" "tgt\<^bsub>C\<^esub> g = src\<^bsub>C\<^esub> f"
    "g \<circ>\<^bsub>C\<^esub> f = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f)" "f \<circ>\<^bsub>C\<^esub> g = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f)"
    using f by (rule isoE)
  have l: "F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f = id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f))"
    using C F fA g by (simp add: functor_comp[symmetric])
  have r: "F \<cdot>\<^sub>a f \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a g = id\<^bsub>D\<^esub> (tgt\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f))"
    using C F fA g by (simp add: functor_comp[symmetric])
  show ?thesis
    by (rule isoI[where g = "F \<cdot>\<^sub>a g"]) (use C F fA g l r in simp_all)
qed

text \<open>
  The rules for \<open>agree\<close> and \<open>nat_trans\<close> are in \<open>Functor\<close>; two of them have a second name here,
  used in \<open>Localization\<close>.
\<close>

lemmas nat_trans_intro = nat_transI
lemmas nat_trans_natural = nat_trans_nat

end
