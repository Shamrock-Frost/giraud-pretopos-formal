section \<open>Notation\<close>

theory Notation
  imports Main
begin

text \<open>
  The symbols \<open>\<in> \<notin> \<subseteq> \<subset> \<inter> \<union> \<times>\<close> are wanted for classes. HOL binds them to its own sets, and two
  readings of one symbol make every formula ambiguous to the parser, so HOL's bindings are
  removed here. HOL sets are still there under their names (\<open>Set.member\<close>, \<open>inf\<close>, ...); only the
  infix notation is gone. Nothing else in \<open>Main\<close> is changed.
\<close>

no_notation
  Set.member  (\<open>'(\<in>')\<close>) and
  Set.member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50) and
  Set.not_member  (\<open>'(\<notin>')\<close>) and
  Set.not_member  (\<open>(\<open>notation=\<open>infix \<notin>\<close>\<close>_/ \<notin> _)\<close> [51, 51] 50) and
  Set.subset  (\<open>'(\<subset>')\<close>) and
  Set.subset  (\<open>(\<open>notation=\<open>infix \<subset>\<close>\<close>_/ \<subset> _)\<close> [51, 51] 50) and
  Set.subset_eq  (\<open>'(\<subseteq>')\<close>) and
  Set.subset_eq  (\<open>(\<open>notation=\<open>infix \<subseteq>\<close>\<close>_/ \<subseteq> _)\<close> [51, 51] 50) and
  Set.inter  (infixl \<open>\<inter>\<close> 70) and
  Set.union  (infixl \<open>\<union>\<close> 65) and
  Product_Type.Times  (infixr \<open>\<times>\<close> 80)

end
