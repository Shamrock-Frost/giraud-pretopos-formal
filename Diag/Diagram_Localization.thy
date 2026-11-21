section \<open>Small presheaves are small diagrams up to final reindexing\<close>

theory Diagram_Localization
  imports Colim_Inverts Spans
begin

text \<open>
  Theorem 3.2 of the note, in NBG, for a locally small category \<open>C\<close> that may be a proper class:
  the functor \<open>colim_functor C : Diag C \<rightarrow> PSh C\<close> is the localization of the category of small
  diagrams at the class \<open>W0 C\<close> of final reindexings.
\<close>

text \<open>
  The proof is the span criterion (Lemma 3.3, \<open>span_localization\<close>) applied to the two
  categories, the functor, and its four hypotheses, each proved in its own theory.
\<close>

theorem diagram_localization:
  assumes "category C" and "locally_small C"
  shows "strict_localization (colim_functor C) (W0 C) (Diag C) (PSh C)"
proof (rule span_localization)
  show "category (Diag C)" by (rule Diag_category[OF assms(1)])
  show "category (PSh C)" by (rule PSh_category[OF assms])
  show "is_functor (colim_functor C) (Diag C) (PSh C)" by (rule colim_functor(1)[OF assms])
  show "identity_on_objects (colim_functor C) (Diag C) (PSh C)" by (rule colim_functor(2)[OF assms])
  show "multiplicative (W0 C) (Diag C)" by (rule W0_multiplicative[OF assms(1)])
  show "inverts (colim_functor C) (W0 C) (PSh C)" by (rule colim_inverts_W0[OF assms])
  show "has_spans (colim_functor C) (W0 C) (Diag C) (PSh C)" by (rule colim_has_spans[OF assms])
  show "has_sections (colim_functor C) (W0 C) (Diag C)" by (rule colim_has_sections[OF assms])
qed

text \<open>
  Hence \<open>PSh C\<close> is also the localization at the class of all morphisms that the functor
  inverts, which was the original question.
\<close>

corollary diagram_localization_at_inverted:
  assumes "category C" and "locally_small C"
  shows "strict_localization (colim_functor C)
    \<lbrace>a. a \<in> Arr (Diag C) \<and> iso (PSh C) (colim_functor C \<cdot>\<^sub>a a)\<rbrace> (Diag C) (PSh C)"
proof (rule strict_localization_at_inverted[OF diagram_localization[OF assms]])
  show "w \<in> Arr (Diag C)" if "w \<in> W0 C" for w
    using W0_multiplicative[OF assms(1)] that unfolding multiplicative_def
    by (blast dest: mem_M)
qed

text \<open>
  A functor that inverts the final reindexings inverts every morphism that the colimit functor
  inverts.
\<close>

theorem inverts_all_inverted:
  assumes "category C" and "locally_small C" and "category N" and "is_functor B (Diag C) N"
    and "inverts B (W0 C) N"
  shows "inverts B \<lbrace>a. a \<in> Arr (Diag C) \<and> iso (PSh C) (colim_functor C \<cdot>\<^sub>a a)\<rbrace> N"
  by (rule localization_inverts_all_inverted[OF diagram_localization[OF assms(1,2)]
        PSh_category[OF assms(1,2)] assms(3-5)])

end
