section \<open>The axioms of NBG that this development does not use\<close>

theory Axioms_Rest
  imports Axioms
begin

text \<open>
  Infinity and regularity complete Mendelson's NBG (he treats regularity and choice as optional
  extras). They are stated here for the record, in a theory that nothing else imports, so the
  theorems of the development visibly do not rest on them. Global choice is not stated at all.
\<close>

axiomatization where
  infinity:
    "\<exists>x. M x \<and> (\<exists>e. e \<in> x \<and> (\<forall>y. y \<notin> e)) \<and>
      (\<forall>u. u \<in> x \<longrightarrow> (\<exists>s. s \<in> x \<and> (\<forall>w. w \<in> s \<longleftrightarrow> w \<in> u \<or> w = u)))" and
  regularity: "\<forall>X. (\<exists>y. y \<in> X) \<longrightarrow> (\<exists>y. y \<in> X \<and> \<not> (\<exists>u. u \<in> y \<and> u \<in> X))"

end
