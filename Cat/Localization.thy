section \<open>A criterion for a functor to be a localization\<close>

theory Localization
  imports Iso
begin

text \<open>
  Lemma 3.3 of the note, for a functor \<open>A : D \<rightarrow> E\<close> that is the identity on objects. (The note
  allows \<open>A\<close> essentially surjective and reduces to this case; the reduction picks preimages of
  objects, and here the functor of interest is the identity on objects from the start.)

  \<open>W\<close> is a class of arrows of \<open>D\<close> that contains the identities and is closed under composition.

  (a) Every arrow \<open>\<phi> : x \<rightarrow> y\<close> of \<open>E\<close> is the right leg of a span: there are \<open>q : x' \<rightarrow> x\<close> in \<open>W\<close> and
      \<open>t : x' \<rightarrow> y\<close> in \<open>D\<close> with \<open>A t = \<phi> \<circ> A q\<close>.

  (b) If \<open>f, g : x \<rightarrow> y\<close> in \<open>D\<close> have \<open>A f = A g\<close>, there are \<open>q : x' \<rightarrow> x\<close> in \<open>W\<close>, \<open>t : x' \<rightarrow> y\<close>, and two
      sections \<open>s, s' : x \<rightarrow> x'\<close> of \<open>q\<close> with \<open>t \<circ> s = f\<close> and \<open>t \<circ> s' = g\<close>.
\<close>

definition identity_on_objects :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "identity_on_objects A D E \<longleftrightarrow>
    (\<forall>\<^sub>s x. x \<in> Ob D \<longrightarrow> x \<in> Ob E \<and> A \<cdot>\<^sub>o x = x) \<and> (\<forall>\<^sub>s y. y \<in> Ob E \<longrightarrow> y \<in> Ob D)"

definition multiplicative :: "cls \<Rightarrow> cls \<Rightarrow> bool"
  where "multiplicative W D \<longleftrightarrow>
    (\<forall>\<^sub>s w. w \<in> W \<longrightarrow> w \<in> Arr D) \<and>
    (\<forall>\<^sub>s x. x \<in> Ob D \<longrightarrow> id\<^bsub>D\<^esub> x \<in> W) \<and>
    (\<forall>\<^sub>s v w. v \<in> W \<longrightarrow> w \<in> W \<longrightarrow> src\<^bsub>D\<^esub> w = tgt\<^bsub>D\<^esub> v \<longrightarrow> w \<circ>\<^bsub>D\<^esub> v \<in> W)"

definition has_spans :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "has_spans A W D E \<longleftrightarrow>
    (\<forall>\<^sub>s \<phi>. \<phi> \<in> Arr E \<longrightarrow>
      (\<exists>\<^sub>s q t. q \<in> W \<and> t \<in> Arr D \<and> src\<^bsub>D\<^esub> t = src\<^bsub>D\<^esub> q \<and>
        tgt\<^bsub>D\<^esub> q = src\<^bsub>E\<^esub> \<phi> \<and> tgt\<^bsub>D\<^esub> t = tgt\<^bsub>E\<^esub> \<phi> \<and> A \<cdot>\<^sub>a t = \<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q))"

definition has_sections :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "has_sections A W D \<longleftrightarrow>
    (\<forall>\<^sub>s f g. f \<in> Arr D \<longrightarrow> g \<in> Arr D \<longrightarrow> src\<^bsub>D\<^esub> f = src\<^bsub>D\<^esub> g \<longrightarrow> tgt\<^bsub>D\<^esub> f = tgt\<^bsub>D\<^esub> g \<longrightarrow>
      A \<cdot>\<^sub>a f = A \<cdot>\<^sub>a g \<longrightarrow>
      (\<exists>\<^sub>s q t s s'. q \<in> W \<and> t \<in> Arr D \<and> s \<in> Arr D \<and> s' \<in> Arr D \<and>
        tgt\<^bsub>D\<^esub> q = src\<^bsub>D\<^esub> f \<and> src\<^bsub>D\<^esub> t = src\<^bsub>D\<^esub> q \<and> tgt\<^bsub>D\<^esub> t = tgt\<^bsub>D\<^esub> f \<and>
        src\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> f \<and> tgt\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> q \<and> src\<^bsub>D\<^esub> s' = src\<^bsub>D\<^esub> f \<and> tgt\<^bsub>D\<^esub> s' = src\<^bsub>D\<^esub> q \<and>
        q \<circ>\<^bsub>D\<^esub> s = id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f) \<and> q \<circ>\<^bsub>D\<^esub> s' = id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f) \<and>
        t \<circ>\<^bsub>D\<^esub> s = f \<and> t \<circ>\<^bsub>D\<^esub> s' = g))"

subsection \<open>Spans and the extension of a functor along them\<close>

text \<open>
  \<open>is_span A W D E \<phi> q t\<close>: the pair \<open>(q, t)\<close> is a span for the arrow \<open>\<phi>\<close> of \<open>E\<close>, as in (a).
  \<open>lifts A W D E N B \<phi> n\<close>: the arrow \<open>n : B (src \<phi>) \<rightarrow> B (tgt \<phi>)\<close> of \<open>N\<close> satisfies \<open>n \<circ> B q = B t\<close> for
  some span \<open>(q, t)\<close> of \<open>\<phi>\<close>; when \<open>B\<close> inverts \<open>W\<close> this says \<open>n = B t \<circ> (B q)⁻¹\<close>. The extension of \<open>B\<close>
  along \<open>A\<close> is \<open>B\<close> on objects and the class of these pairs \<open>\<langle>\<phi>, n\<rangle>\<close> on arrows: it is defined by
  comprehension, with no choice of a span.
\<close>

definition is_span :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "is_span A W D E \<phi> q t \<longleftrightarrow> q \<in> W \<and> t \<in> Arr D \<and> src\<^bsub>D\<^esub> t = src\<^bsub>D\<^esub> q \<and>
    tgt\<^bsub>D\<^esub> q = src\<^bsub>E\<^esub> \<phi> \<and> tgt\<^bsub>D\<^esub> t = tgt\<^bsub>E\<^esub> \<phi> \<and> A \<cdot>\<^sub>a t = \<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q"

definition lifts :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "lifts A W D E N B \<phi> n \<longleftrightarrow> \<phi> \<in> Arr E \<and> n \<in> Arr N \<and>
    src\<^bsub>N\<^esub> n = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> \<phi> \<and> tgt\<^bsub>N\<^esub> n = B \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> \<phi> \<and>
    (\<exists>\<^sub>s q t. is_span A W D E \<phi> q t \<and> n \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = B \<cdot>\<^sub>a t)"

lemma dfn_is_span [dfn_rules]:
  "dcls A \<Longrightarrow> dcls W \<Longrightarrow> dcls D \<Longrightarrow> dcls E \<Longrightarrow> dfun f \<Longrightarrow> dfun q \<Longrightarrow> dfun t \<Longrightarrow>
    dfn (\<lambda>x. is_span (A x) (W x) (D x) (E x) (f x) (q x) (t x))"
  unfolding is_span_def by dfn

lemma dfn_lifts [dfn_rules]:
  "dcls A \<Longrightarrow> dcls W \<Longrightarrow> dcls D \<Longrightarrow> dcls E \<Longrightarrow> dcls N \<Longrightarrow> dcls B \<Longrightarrow> dfun f \<Longrightarrow> dfun n \<Longrightarrow>
    dfn (\<lambda>x. lifts (A x) (W x) (D x) (E x) (N x) (B x) (f x) (n x))"
  unfolding lifts_def by dfn

definition span_lift_arrs :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "span_lift_arrs A W D E N B = \<lbrace>p. \<exists>\<^sub>s \<phi> n. p = \<langle>\<phi>, n\<rangle> \<and> lifts A W D E N B \<phi> n\<rbrace>"

definition span_lift :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "span_lift A W D E N B = mkfun (\<lambda>x\<in>Ob E. B \<cdot>\<^sub>o x) (span_lift_arrs A W D E N B)"

lemma mem_span_lift_arrs:
  "M \<phi> \<Longrightarrow> M n \<Longrightarrow> \<langle>\<phi>, n\<rangle> \<in> span_lift_arrs A W D E N B \<longleftrightarrow> lifts A W D E N B \<phi> n"
  unfolding span_lift_arrs_def by auto

subsection \<open>The hypotheses of the criterion\<close>

text \<open>
  The hypotheses of the theorem, read as rules. \<open>A\<close> is the identity on objects, so the objects
  of \<open>E\<close> are those of \<open>D\<close> and sources and targets of \<open>A f\<close> are those of \<open>f\<close>.
\<close>

locale span_criterion =
  fixes A W D E
  assumes D: "category D" and E: "category E" and A: "is_functor A D E"
    and ioo: "identity_on_objects A D E" and mult: "multiplicative W D"
    and invA: "inverts A W E" and spans: "has_spans A W D E" and sections: "has_sections A W D"
begin

lemma Ob_E [simp]: "x \<in> Ob E \<longleftrightarrow> x \<in> Ob D"
  using ioo unfolding identity_on_objects_def by (blast dest: mem_M)

lemma A_obj [simp]: "x \<in> Ob D \<Longrightarrow> A \<cdot>\<^sub>o x = x"
  using ioo unfolding identity_on_objects_def by (blast dest: mem_M)

lemma E_src [simp]: "\<phi> \<in> Arr E \<Longrightarrow> src\<^bsub>E\<^esub> \<phi> \<in> Ob D"
  using cat_src[OF E] by simp

lemma E_tgt [simp]: "\<phi> \<in> Arr E \<Longrightarrow> tgt\<^bsub>E\<^esub> \<phi> \<in> Ob D"
  using cat_tgt[OF E] by simp

lemma A_arr [simp]: "f \<in> Arr D \<Longrightarrow> A \<cdot>\<^sub>a f \<in> Arr E"
  using A by simp

lemma A_src [simp]: "f \<in> Arr D \<Longrightarrow> src\<^bsub>E\<^esub> (A \<cdot>\<^sub>a f) = src\<^bsub>D\<^esub> f"
  using A D by simp

lemma A_tgt [simp]: "f \<in> Arr D \<Longrightarrow> tgt\<^bsub>E\<^esub> (A \<cdot>\<^sub>a f) = tgt\<^bsub>D\<^esub> f"
  using A D by simp

lemma A_id [simp]: "x \<in> Ob D \<Longrightarrow> A \<cdot>\<^sub>a id\<^bsub>D\<^esub> x = id\<^bsub>E\<^esub> x"
  using A by simp

lemma A_comp: "f \<in> Arr D \<Longrightarrow> g \<in> Arr D \<Longrightarrow> src\<^bsub>D\<^esub> g = tgt\<^bsub>D\<^esub> f \<Longrightarrow> A \<cdot>\<^sub>a (g \<circ>\<^bsub>D\<^esub> f) = A \<cdot>\<^sub>a g \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a f"
  using A by (rule functor_comp)

lemma W_arr [simp]: "w \<in> W \<Longrightarrow> w \<in> Arr D"
  using mult unfolding multiplicative_def by (blast dest: mem_M)

lemma W_id [simp]: "x \<in> Ob D \<Longrightarrow> id\<^bsub>D\<^esub> x \<in> W"
  using mult unfolding multiplicative_def by (blast dest: mem_M)

lemma W_comp: "v \<in> W \<Longrightarrow> w \<in> W \<Longrightarrow> src\<^bsub>D\<^esub> w = tgt\<^bsub>D\<^esub> v \<Longrightarrow> w \<circ>\<^bsub>D\<^esub> v \<in> W"
  using mult unfolding multiplicative_def by (blast dest: mem_M)

lemma A_iso: "w \<in> W \<Longrightarrow> iso E (A \<cdot>\<^sub>a w)"
  using invA unfolding inverts_def by (blast dest: mem_M)

lemma is_spanD:
  assumes "is_span A W D E \<phi> q t"
  shows "q \<in> W" "q \<in> Arr D" "t \<in> Arr D" "src\<^bsub>D\<^esub> t = src\<^bsub>D\<^esub> q" "tgt\<^bsub>D\<^esub> q = src\<^bsub>E\<^esub> \<phi>"
    "tgt\<^bsub>D\<^esub> t = tgt\<^bsub>E\<^esub> \<phi>"
  using assms unfolding is_span_def by simp_all

lemma is_span_eq: "is_span A W D E \<phi> q t \<Longrightarrow> A \<cdot>\<^sub>a t = \<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q"
  unfolding is_span_def by simp

lemma span_exists:
  assumes "\<phi> \<in> Arr E"
  obtains q t where "is_span A W D E \<phi> q t"
  using spans assms unfolding has_spans_def is_span_def by (blast dest: mem_M)

lemma sections_exist:
  assumes "f \<in> Arr D" and "g \<in> Arr D" and "src\<^bsub>D\<^esub> f = src\<^bsub>D\<^esub> g" and "tgt\<^bsub>D\<^esub> f = tgt\<^bsub>D\<^esub> g"
    and "A \<cdot>\<^sub>a f = A \<cdot>\<^sub>a g"
  obtains q t s s' where "q \<in> W" "t \<in> Arr D" "s \<in> Arr D" "s' \<in> Arr D"
    "tgt\<^bsub>D\<^esub> q = src\<^bsub>D\<^esub> f" "src\<^bsub>D\<^esub> t = src\<^bsub>D\<^esub> q" "tgt\<^bsub>D\<^esub> t = tgt\<^bsub>D\<^esub> f"
    "src\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> f" "tgt\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> q" "src\<^bsub>D\<^esub> s' = src\<^bsub>D\<^esub> f" "tgt\<^bsub>D\<^esub> s' = src\<^bsub>D\<^esub> q"
    "q \<circ>\<^bsub>D\<^esub> s = id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f)" "q \<circ>\<^bsub>D\<^esub> s' = id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f)" "t \<circ>\<^bsub>D\<^esub> s = f" "t \<circ>\<^bsub>D\<^esub> s' = g"
proof -
  have "M f" "M g"
    using assms by (simp_all add: mem_M)
  then show ?thesis
    using sections assms that unfolding has_sections_def by blast
qed

text \<open>
  Spans can be completed to commutative squares up to \<open>A\<close>: for \<open>q\<close> in \<open>W\<close> and \<open>u\<close> with the same
  target there are \<open>r\<close> in \<open>W\<close> and \<open>s\<close> with \<open>A (q \<circ> s) = A (u \<circ> r)\<close>. This is (a) applied to
  \<open>(A q)⁻¹ \<circ> A u\<close>.
\<close>

lemma complete_square:
  assumes q: "q \<in> W" and u: "u \<in> Arr D" and uq: "tgt\<^bsub>D\<^esub> u = tgt\<^bsub>D\<^esub> q"
  obtains r s where "r \<in> W" "s \<in> Arr D" "src\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> r" "tgt\<^bsub>D\<^esub> r = src\<^bsub>D\<^esub> u"
    "tgt\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> q" "A \<cdot>\<^sub>a (q \<circ>\<^bsub>D\<^esub> s) = A \<cdot>\<^sub>a (u \<circ>\<^bsub>D\<^esub> r)"
proof -
  have qD: "q \<in> Arr D"
    using q by simp
  obtain a where a: "a \<in> Arr E" "src\<^bsub>E\<^esub> a = tgt\<^bsub>E\<^esub> (A \<cdot>\<^sub>a q)" "tgt\<^bsub>E\<^esub> a = src\<^bsub>E\<^esub> (A \<cdot>\<^sub>a q)"
    "a \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q = id\<^bsub>E\<^esub> (src\<^bsub>E\<^esub> (A \<cdot>\<^sub>a q))" "A \<cdot>\<^sub>a q \<circ>\<^bsub>E\<^esub> a = id\<^bsub>E\<^esub> (tgt\<^bsub>E\<^esub> (A \<cdot>\<^sub>a q))"
    using A_iso[OF q] by (rule isoE)
  have a': "src\<^bsub>E\<^esub> a = tgt\<^bsub>D\<^esub> q" "tgt\<^bsub>E\<^esub> a = src\<^bsub>D\<^esub> q" "A \<cdot>\<^sub>a q \<circ>\<^bsub>E\<^esub> a = id\<^bsub>E\<^esub> (tgt\<^bsub>D\<^esub> q)"
    using a qD by simp_all
  define \<chi> where "\<chi> = a \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a u"
  have \<chi>: "\<chi> \<in> Arr E" "src\<^bsub>E\<^esub> \<chi> = src\<^bsub>D\<^esub> u" "tgt\<^bsub>E\<^esub> \<chi> = src\<^bsub>D\<^esub> q"
    using E a(1) a' u uq unfolding \<chi>_def by simp_all
  obtain r s where sp: "is_span A W D E \<chi> r s"
    using \<chi>(1) by (rule span_exists)
  note rs = is_spanD[OF sp]
  have rs': "src\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> r" "tgt\<^bsub>D\<^esub> r = src\<^bsub>D\<^esub> u" "tgt\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> q"
    using rs \<chi> by simp_all
  have "A \<cdot>\<^sub>a (q \<circ>\<^bsub>D\<^esub> s) = A \<cdot>\<^sub>a q \<circ>\<^bsub>E\<^esub> ((a \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a u) \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a r)"
    using A_comp[OF rs(3) qD] rs' is_span_eq[OF sp] by (simp add: \<chi>_def)
  also have "\<dots> = (A \<cdot>\<^sub>a q \<circ>\<^bsub>E\<^esub> a) \<circ>\<^bsub>E\<^esub> (A \<cdot>\<^sub>a u \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a r)"
    using E a(1) a' u uq rs rs' qD by (simp add: cat_assoc)
  also have "\<dots> = A \<cdot>\<^sub>a u \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a r"
    using E a(1) a' u uq rs rs' qD by simp
  also have "\<dots> = A \<cdot>\<^sub>a (u \<circ>\<^bsub>D\<^esub> r)"
    using A_comp[OF rs(2) u] rs' by simp
  finally show ?thesis
    using that rs rs' by blast
qed

end

subsection \<open>A functor that inverts \<open>W\<close>\<close>

locale span_target = span_criterion A W D E
  for A W D E +
  fixes N B
  assumes N: "category N" and B: "is_functor B D N" and invB: "inverts B W N"
begin

lemma B_obj [simp]: "x \<in> Ob D \<Longrightarrow> B \<cdot>\<^sub>o x \<in> Ob N"
  using B by simp

lemma B_arr [simp]: "f \<in> Arr D \<Longrightarrow> B \<cdot>\<^sub>a f \<in> Arr N"
  using B by simp

lemma B_src [simp]: "f \<in> Arr D \<Longrightarrow> src\<^bsub>N\<^esub> (B \<cdot>\<^sub>a f) = B \<cdot>\<^sub>o src\<^bsub>D\<^esub> f"
  using B by simp

lemma B_tgt [simp]: "f \<in> Arr D \<Longrightarrow> tgt\<^bsub>N\<^esub> (B \<cdot>\<^sub>a f) = B \<cdot>\<^sub>o tgt\<^bsub>D\<^esub> f"
  using B by simp

lemma B_id [simp]: "x \<in> Ob D \<Longrightarrow> B \<cdot>\<^sub>a id\<^bsub>D\<^esub> x = id\<^bsub>N\<^esub> (B \<cdot>\<^sub>o x)"
  using B by simp

lemma B_comp:"f \<in> Arr D \<Longrightarrow> g \<in> Arr D \<Longrightarrow> src\<^bsub>D\<^esub> g = tgt\<^bsub>D\<^esub> f \<Longrightarrow> B \<cdot>\<^sub>a (g \<circ>\<^bsub>D\<^esub> f) = B \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a f"
  using B by (rule functor_comp)

lemma B_iso: "w \<in> W \<Longrightarrow> iso N (B \<cdot>\<^sub>a w)"
  using invB unfolding inverts_def by (blast dest: mem_M)

text \<open>Step 0: parallel arrows that \<open>A\<close> identifies, \<open>B\<close> identifies too.\<close>

lemma B_eq:
  assumes f: "f \<in> Arr D" and g: "g \<in> Arr D" and st: "src\<^bsub>D\<^esub> f = src\<^bsub>D\<^esub> g" "tgt\<^bsub>D\<^esub> f = tgt\<^bsub>D\<^esub> g"
    and Afg: "A \<cdot>\<^sub>a f = A \<cdot>\<^sub>a g"
  shows "B \<cdot>\<^sub>a f = B \<cdot>\<^sub>a g"
proof -
  obtain q t s s' where q: "q \<in> W" and t: "t \<in> Arr D" and s: "s \<in> Arr D" and s': "s' \<in> Arr D"
    and h: "tgt\<^bsub>D\<^esub> q = src\<^bsub>D\<^esub> f" "src\<^bsub>D\<^esub> t = src\<^bsub>D\<^esub> q" "tgt\<^bsub>D\<^esub> t = tgt\<^bsub>D\<^esub> f"
      "src\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> f" "tgt\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> q" "src\<^bsub>D\<^esub> s' = src\<^bsub>D\<^esub> f" "tgt\<^bsub>D\<^esub> s' = src\<^bsub>D\<^esub> q"
    and qs: "q \<circ>\<^bsub>D\<^esub> s = id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f)" "q \<circ>\<^bsub>D\<^esub> s' = id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f)"
    and ts: "t \<circ>\<^bsub>D\<^esub> s = f" "t \<circ>\<^bsub>D\<^esub> s' = g"
    using sections_exist[OF f g st Afg] by blast
  have qD: "q \<in> Arr D"
    using q by simp
  have "B \<cdot>\<^sub>a q \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a s = B \<cdot>\<^sub>a q \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a s'"
    using B_comp[OF s qD] B_comp[OF s' qD] qs h by simp
  then have bs: "B \<cdot>\<^sub>a s = B \<cdot>\<^sub>a s'"
    by (rule iso_cancel_left[OF N B_iso[OF q], rotated -1]) (use s s' h qD in simp_all)
  have "B \<cdot>\<^sub>a f = B \<cdot>\<^sub>a t \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a s"
    using B_comp[OF s t] ts h by simp
  also have "\<dots> = B \<cdot>\<^sub>a g"
    using B_comp[OF s' t] ts h bs by simp
  finally show ?thesis .
qed

text \<open>
  Step 1: an arrow of \<open>E\<close> has at most one lift. Two spans \<open>(q1, t1)\<close> and \<open>(q2, t2)\<close> of \<open>\<phi>\<close> are joined by
  a square \<open>A (q2 \<circ> s) = A (q1 \<circ> r)\<close>; then \<open>A (t2 \<circ> s) = A (t1 \<circ> r)\<close>, Step 0 carries both equations
  through \<open>B\<close>, and the two lifts agree after composing with the isomorphism \<open>B (q1 \<circ> r)\<close>.
\<close>

lemma lifts_unique:
  assumes 1: "lifts A W D E N B \<phi> na" and 2: "lifts A W D E N B \<phi> nb"
  shows "na = nb"
proof -
  obtain q1 t1 where \<phi>: "\<phi> \<in> Arr E" and n1: "na \<in> Arr N" "src\<^bsub>N\<^esub> na = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> \<phi>"
      and sp1: "is_span A W D E \<phi> q1 t1" and e1: "na \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q1 = B \<cdot>\<^sub>a t1"
    using 1 unfolding lifts_def by blast
  obtain q2 t2 where n2: "nb \<in> Arr N" "src\<^bsub>N\<^esub> nb = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> \<phi>"
      and sp2: "is_span A W D E \<phi> q2 t2" and e2: "nb \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q2 = B \<cdot>\<^sub>a t2"
    using 2 unfolding lifts_def by blast
  note s1 = is_spanD[OF sp1] and s2 = is_spanD[OF sp2]
  have "tgt\<^bsub>D\<^esub> q1 = tgt\<^bsub>D\<^esub> q2"
    using s1 s2 by simp
  then obtain r s where r: "r \<in> W" and s: "s \<in> Arr D"
      and rs: "src\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> r" "tgt\<^bsub>D\<^esub> r = src\<^bsub>D\<^esub> q1" "tgt\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> q2"
      and sq: "A \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s) = A \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r)"
    using complete_square[OF s2(1) s1(2)] by blast
  have rD: "r \<in> Arr D"
    using r by simp
  have At: "A \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s) = A \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
  proof -
    have "A \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s) = (\<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q2) \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a s"
      using A_comp[OF s s2(3)] is_span_eq[OF sp2] rs s2 by simp
    also have "\<dots> = \<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s)"
      using E \<phi> s s2 rs A_comp[OF s s2(2)] by (simp add: cat_assoc)
    also have "\<dots> = \<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r)"
      by (simp add: sq)
    also have "\<dots> = (\<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q1) \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a r"
      using E \<phi> rD s1 rs A_comp[OF rD s1(2)] by (simp add: cat_assoc)
    also have "\<dots> = A \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
      using A_comp[OF rD s1(3)] is_span_eq[OF sp1] rs s1 by simp
    finally show ?thesis .
  qed
  have Bq: "B \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s) = B \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r)"
    by (rule B_eq[OF _ _ _ _ sq]) (use D s rD s1 s2 rs in simp_all)
  have Bt: "B \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s) = B \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
    by (rule B_eq[OF _ _ _ _ At]) (use D s rD s1 s2 rs in simp_all)
  define w where "w = q1 \<circ>\<^bsub>D\<^esub> r"
  have w: "w \<in> W"
    using W_comp[OF r s1(1)] rs unfolding w_def by simp
  have wD: "w \<in> Arr D" and wt: "tgt\<^bsub>D\<^esub> w = src\<^bsub>E\<^esub> \<phi>"
    using D rD s1 rs unfolding w_def by simp_all
  have "na \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a w = nb \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a w"
  proof -
    have "na \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a w = (na \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q1) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a r"
      using N n1 rD s1 rs B_comp[OF rD s1(2)] unfolding w_def by (simp add: cat_assoc)
    also have "\<dots> = B \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
      using e1 B_comp[OF rD s1(3)] rs s1 by simp
    also have "\<dots> = B \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s)"
      by (simp add: Bt)
    also have "\<dots> = (nb \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q2) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a s"
      using e2 B_comp[OF s s2(3)] rs s2 by simp
    also have "\<dots> = nb \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s)"
      using N n2 s s2 rs B_comp[OF s s2(2)] by (simp add: cat_assoc)
    also have "\<dots> = nb \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a w"
      by (simp add: Bq w_def)
    finally show ?thesis .
  qed
  then show ?thesis
    by (rule iso_cancel_right[OF N B_iso[OF w], rotated -1]) (use n1 n2 wD wt in simp_all)
qed

text \<open>Every span of an arrow gives a lift: \<open>B t \<circ> b\<close> for an inverse \<open>b\<close> of \<open>B q\<close>.\<close>

lemma lifts_of_span:
  assumes \<phi>: "\<phi> \<in> Arr E" and sp: "is_span A W D E \<phi> q t"
  obtains n where "lifts A W D E N B \<phi> n" and "n \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = B \<cdot>\<^sub>a t"
proof -
  note st = is_spanD[OF sp]
  obtain b where b: "b \<in> Arr N" "src\<^bsub>N\<^esub> b = tgt\<^bsub>N\<^esub> (B \<cdot>\<^sub>a q)" "tgt\<^bsub>N\<^esub> b = src\<^bsub>N\<^esub> (B \<cdot>\<^sub>a q)"
    "b \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = id\<^bsub>N\<^esub> (src\<^bsub>N\<^esub> (B \<cdot>\<^sub>a q))" "B \<cdot>\<^sub>a q \<circ>\<^bsub>N\<^esub> b = id\<^bsub>N\<^esub> (tgt\<^bsub>N\<^esub> (B \<cdot>\<^sub>a q))"
    using B_iso[OF st(1)] by (rule isoE)
  have b': "src\<^bsub>N\<^esub> b = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> \<phi>" "tgt\<^bsub>N\<^esub> b = B \<cdot>\<^sub>o src\<^bsub>D\<^esub> q"
    "b \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = id\<^bsub>N\<^esub> (B \<cdot>\<^sub>o src\<^bsub>D\<^esub> q)"
    using b st by simp_all
  define n where "n = B \<cdot>\<^sub>a t \<circ>\<^bsub>N\<^esub> b"
  have n: "n \<in> Arr N" "src\<^bsub>N\<^esub> n = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> \<phi>" "tgt\<^bsub>N\<^esub> n = B \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> \<phi>"
    using N b(1) b' st unfolding n_def by simp_all
  have e: "n \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = B \<cdot>\<^sub>a t"
  proof -
    have "n \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = B \<cdot>\<^sub>a t \<circ>\<^bsub>N\<^esub> (b \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q)"
      using N b(1) b'(1,2) st unfolding n_def by (simp add: cat_assoc)
    also have "\<dots> = B \<cdot>\<^sub>a t"
      using N b' st by simp
    finally show ?thesis .
  qed
  have "M q" "M t"
    using st by (simp_all add: mem_M)
  then have "lifts A W D E N B \<phi> n"
    unfolding lifts_def using \<phi> n sp e by blast
  then show ?thesis
    using e by (rule that)
qed

text \<open>The extension \<open>L\<close> of \<open>B\<close> reads its value on an arrow off any lift, hence off any span.\<close>

abbreviation L where "L \<equiv> span_lift A W D E N B"

lemma lift_eq:
  assumes "lifts A W D E N B \<phi> n"
  shows "L \<cdot>\<^sub>a \<phi> = n"
proof -
  have \<phi>: "\<phi> \<in> Arr E" and nN: "n \<in> Arr N"
    using assms unfolding lifts_def by simp_all
  have "span_lift_arrs A W D E N B \<cdot> \<phi> = n"
  proof (rule app_eq)
    show "M n"
      using nN by (rule mem_M)
    show "\<langle>\<phi>, n\<rangle> \<in> span_lift_arrs A W D E N B"
      using assms \<phi> nN by (simp add: mem_span_lift_arrs mem_M)
  next
    fix n' assume "M n'" and "\<langle>\<phi>, n'\<rangle> \<in> span_lift_arrs A W D E N B"
    then have "lifts A W D E N B \<phi> n'"
      using \<phi> by (simp add: mem_span_lift_arrs mem_M)
    then show "n' = n"
      using assms by (rule lifts_unique)
  qed
  then show ?thesis
    by (simp add: span_lift_def)
qed

lemma lift_obj [simp]: "x \<in> Ob D \<Longrightarrow> L \<cdot>\<^sub>o x = B \<cdot>\<^sub>o x"
  by (simp add: span_lift_def)

lemma lift_span:
  assumes "\<phi> \<in> Arr E" and "is_span A W D E \<phi> q t"
  shows "L \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = B \<cdot>\<^sub>a t"
proof -
  obtain n where "lifts A W D E N B \<phi> n" and "n \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = B \<cdot>\<^sub>a t"
    using assms by (rule lifts_of_span)
  then show ?thesis
    by (simp add: lift_eq)
qed

lemma lift_arr:
  assumes \<phi>: "\<phi> \<in> Arr E"
  shows "L \<cdot>\<^sub>a \<phi> \<in> Arr N" "src\<^bsub>N\<^esub> (L \<cdot>\<^sub>a \<phi>) = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> \<phi>" "tgt\<^bsub>N\<^esub> (L \<cdot>\<^sub>a \<phi>) = B \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> \<phi>"
proof -
  obtain q t where "is_span A W D E \<phi> q t"
    using \<phi> by (rule span_exists)
  then obtain n where n: "lifts A W D E N B \<phi> n"
    using \<phi> lifts_of_span by blast
  then have "L \<cdot>\<^sub>a \<phi> = n"
    by (rule lift_eq)
  then show "L \<cdot>\<^sub>a \<phi> \<in> Arr N" "src\<^bsub>N\<^esub> (L \<cdot>\<^sub>a \<phi>) = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> \<phi>" "tgt\<^bsub>N\<^esub> (L \<cdot>\<^sub>a \<phi>) = B \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> \<phi>"
    using n unfolding lifts_def by simp_all
qed

text \<open>
  \<open>L\<close> is a functor. Identities lift along the span \<open>(id, id)\<close>. For \<open>\<psi> \<circ> \<phi>\<close>, with spans \<open>(q1, t1)\<close> of \<open>\<phi>\<close>
  and \<open>(q2, t2)\<close> of \<open>\<psi>\<close>, a square \<open>A (q2 \<circ> s) = A (t1 \<circ> r)\<close> gives the span \<open>(q1 \<circ> r, t2 \<circ> s)\<close> of
  \<open>\<psi> \<circ> \<phi>\<close>, and \<open>L \<psi> \<circ> L \<phi>\<close> satisfies the lift equation for it.
\<close>

lemma lift_id: "x \<in> Ob D \<Longrightarrow> L \<cdot>\<^sub>a id\<^bsub>E\<^esub> x = id\<^bsub>N\<^esub> (B \<cdot>\<^sub>o x)"
proof -
  assume x: "x \<in> Ob D"
  have sp: "is_span A W D E (id\<^bsub>E\<^esub> x) (id\<^bsub>D\<^esub> x) (id\<^bsub>D\<^esub> x)"
    unfolding is_span_def using D E x by simp
  have "L \<cdot>\<^sub>a id\<^bsub>E\<^esub> x \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a id\<^bsub>D\<^esub> x = B \<cdot>\<^sub>a id\<^bsub>D\<^esub> x"
    using lift_span[OF _ sp] E x by simp
  moreover have "L \<cdot>\<^sub>a id\<^bsub>E\<^esub> x \<in> Arr N" "src\<^bsub>N\<^esub> (L \<cdot>\<^sub>a id\<^bsub>E\<^esub> x) = B \<cdot>\<^sub>o x"
    using E x lift_arr[of "id\<^bsub>E\<^esub> x"] by simp_all
  ultimately show ?thesis
    using N B x by simp
qed

lemma lift_comp:
  assumes f: "f \<in> Arr E" and g: "g \<in> Arr E" and gf: "src\<^bsub>E\<^esub> g = tgt\<^bsub>E\<^esub> f"
  shows "L \<cdot>\<^sub>a (g \<circ>\<^bsub>E\<^esub> f) = L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> L \<cdot>\<^sub>a f"
proof -
  obtain q1 t1 where sp1: "is_span A W D E f q1 t1"
    using f by (rule span_exists)
  obtain q2 t2 where sp2: "is_span A W D E g q2 t2"
    using g by (rule span_exists)
  note s1 = is_spanD[OF sp1] and s2 = is_spanD[OF sp2]
  have "tgt\<^bsub>D\<^esub> t1 = tgt\<^bsub>D\<^esub> q2"
    using s1 s2 gf by simp
  then obtain r s where r: "r \<in> W" and s: "s \<in> Arr D"
      and rs: "src\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> r" "tgt\<^bsub>D\<^esub> r = src\<^bsub>D\<^esub> q1" "tgt\<^bsub>D\<^esub> s = src\<^bsub>D\<^esub> q2"
      and sq: "A \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s) = A \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
    using complete_square[OF s2(1) s1(3)] s1 by auto
  have rD: "r \<in> Arr D"
    using r by simp
  have Bsq: "B \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s) = B \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
    by (rule B_eq[OF _ _ _ _ sq]) (use D s rD s1 s2 rs gf in simp_all)
  have Aeq: "A \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s) = (g \<circ>\<^bsub>E\<^esub> f) \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r)"
  proof -
    have "A \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s) = (g \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q2) \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a s"
      using A_comp[OF s s2(3)] is_span_eq[OF sp2] rs s2 by simp
    also have "\<dots> = g \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s)"
      using E g s s2 rs A_comp[OF s s2(2)] by (simp add: cat_assoc)
    also have "\<dots> = g \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
      by (simp add: sq)
    also have "\<dots> = g \<circ>\<^bsub>E\<^esub> ((f \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q1) \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a r)"
      using A_comp[OF rD s1(3)] is_span_eq[OF sp1] rs s1 by simp
    also have "\<dots> = (g \<circ>\<^bsub>E\<^esub> f) \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r)"
      using E f g gf rD s1 rs A_comp[OF rD s1(2)] by (simp add: cat_assoc)
    finally show ?thesis .
  qed
  have w: "q1 \<circ>\<^bsub>D\<^esub> r \<in> W"
    using W_comp[OF r s1(1)] rs by simp
  have sp: "is_span A W D E (g \<circ>\<^bsub>E\<^esub> f) (q1 \<circ>\<^bsub>D\<^esub> r) (t2 \<circ>\<^bsub>D\<^esub> s)"
    unfolding is_span_def using D E f g gf w rD s s1 s2 rs Aeq by simp
  have Lf: "L \<cdot>\<^sub>a f \<in> Arr N" "src\<^bsub>N\<^esub> (L \<cdot>\<^sub>a f) = B \<cdot>\<^sub>o src\<^bsub>E\<^esub> f" "tgt\<^bsub>N\<^esub> (L \<cdot>\<^sub>a f) = B \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> f"
    using f by (rule lift_arr)+
  have Lg: "L \<cdot>\<^sub>a g \<in> Arr N" "src\<^bsub>N\<^esub> (L \<cdot>\<^sub>a g) = B \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> f" "tgt\<^bsub>N\<^esub> (L \<cdot>\<^sub>a g) = B \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> g"
    using g gf lift_arr[OF g] by simp_all
  have "(L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> L \<cdot>\<^sub>a f) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r) = B \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s)"
  proof -
    have "(L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> L \<cdot>\<^sub>a f) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r)
        = L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> ((L \<cdot>\<^sub>a f \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q1) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a r)"
      using N Lf Lg rD s1 rs B_comp[OF rD s1(2)] by (simp add: cat_assoc)
    also have "\<dots> = L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (t1 \<circ>\<^bsub>D\<^esub> r)"
      using lift_span[OF f sp1] B_comp[OF rD s1(3)] rs s1 by simp
    also have "\<dots> = L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (q2 \<circ>\<^bsub>D\<^esub> s)"
      by (simp add: Bsq)
    also have "\<dots> = (L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q2) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a s"
      using N Lg s s2 rs gf B_comp[OF s s2(2)] by (simp add: cat_assoc)
    also have "\<dots> = B \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s)"
      using lift_span[OF g sp2] B_comp[OF s s2(3)] rs s2 by simp
    finally show ?thesis .
  qed
  moreover have "L \<cdot>\<^sub>a (g \<circ>\<^bsub>E\<^esub> f) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r) = B \<cdot>\<^sub>a (t2 \<circ>\<^bsub>D\<^esub> s)"
    using E f g gf sp by (simp add: lift_span)
  ultimately have "L \<cdot>\<^sub>a (g \<circ>\<^bsub>E\<^esub> f) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r) = (L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> L \<cdot>\<^sub>a f) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a (q1 \<circ>\<^bsub>D\<^esub> r)"
    by simp
  then show ?thesis
    by (rule iso_cancel_right[OF N B_iso[OF w], rotated -1])
      (use D E N f g gf Lf Lg rD s1 rs lift_arr[of "g \<circ>\<^bsub>E\<^esub> f"] in simp_all)
qed

lemma lift_functor: "is_functor L E N"
proof (rule is_functorI)
  fix x assume "x \<in> Ob E"
  then show "L \<cdot>\<^sub>o x \<in> Ob N"
    by simp
next
  fix f assume f: "f \<in> Arr E"
  show "L \<cdot>\<^sub>a f \<in> Arr N"
    using f by (rule lift_arr)
  show "src\<^bsub>N\<^esub> (L \<cdot>\<^sub>a f) = L \<cdot>\<^sub>o src\<^bsub>E\<^esub> f" "tgt\<^bsub>N\<^esub> (L \<cdot>\<^sub>a f) = L \<cdot>\<^sub>o tgt\<^bsub>E\<^esub> f"
    using f lift_arr[OF f] by simp_all
next
  fix x assume "x \<in> Ob E"
  then show "L \<cdot>\<^sub>a id\<^bsub>E\<^esub> x = id\<^bsub>N\<^esub> (L \<cdot>\<^sub>o x)"
    by (simp add: lift_id)
next
  fix f g assume "f \<in> Arr E" "g \<in> Arr E" "src\<^bsub>E\<^esub> g = tgt\<^bsub>E\<^esub> f"
  then show "L \<cdot>\<^sub>a (g \<circ>\<^bsub>E\<^esub> f) = L \<cdot>\<^sub>a g \<circ>\<^bsub>N\<^esub> L \<cdot>\<^sub>a f"
    by (rule lift_comp)
qed

text \<open>\<open>L \<circ> A\<close> is \<open>B\<close>: \<open>A f\<close> has the span \<open>(id, f)\<close>.\<close>

lemma lift_agree: "agree D (fcomp D L A) B"
proof (rule agreeI)
  fix x assume "x \<in> Ob D"
  then show "fcomp D L A \<cdot>\<^sub>o x = B \<cdot>\<^sub>o x"
    by simp
next
  fix f assume f: "f \<in> Arr D"
  have sp: "is_span A W D E (A \<cdot>\<^sub>a f) (id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f)) f"
    unfolding is_span_def using D E f by simp
  have "L \<cdot>\<^sub>a (A \<cdot>\<^sub>a f) \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a id\<^bsub>D\<^esub> (src\<^bsub>D\<^esub> f) = B \<cdot>\<^sub>a f"
    using f sp by (simp add: lift_span)
  moreover have "L \<cdot>\<^sub>a (A \<cdot>\<^sub>a f) \<in> Arr N" "src\<^bsub>N\<^esub> (L \<cdot>\<^sub>a (A \<cdot>\<^sub>a f)) = B \<cdot>\<^sub>o src\<^bsub>D\<^esub> f"
    using f lift_arr[of "A \<cdot>\<^sub>a f"] by simp_all
  ultimately show "fcomp D L A \<cdot>\<^sub>a f = B \<cdot>\<^sub>a f"
    using N D f by simp
qed

text \<open>Uniqueness: a functor \<open>F\<close> with \<open>F \<circ> A = B\<close> satisfies the lift equation on every span, so it is \<open>L\<close>.\<close>

lemma agree_lift:
  assumes F: "is_functor F E N" and FB: "agree D (fcomp D F A) B"
  shows "agree E F L"
proof (rule agreeI)
  fix x assume "x \<in> Ob E"
  then have x: "x \<in> Ob D"
    by simp
  have "F \<cdot>\<^sub>o x = fcomp D F A \<cdot>\<^sub>o x"
    using x by simp
  also have "\<dots> = B \<cdot>\<^sub>o x"
    using FB x by (rule agree_obj)
  finally show "F \<cdot>\<^sub>o x = L \<cdot>\<^sub>o x"
    using x by simp
next
  fix \<phi> assume \<phi>: "\<phi> \<in> Arr E"
  obtain q t where sp: "is_span A W D E \<phi> q t"
    using \<phi> by (rule span_exists)
  note st = is_spanD[OF sp]
  have FA: "\<And>u. u \<in> Arr D \<Longrightarrow> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a u) = B \<cdot>\<^sub>a u"
    using agree_arr[OF FB] by simp
  have "F \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = F \<cdot>\<^sub>a (\<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q)"
    using functor_comp[OF F A_arr[OF st(2)] \<phi>] FA[OF st(2)] st by simp
  also have "\<dots> = B \<cdot>\<^sub>a t"
    using is_span_eq[OF sp] FA[OF st(3)] by simp
  also have "\<dots> = L \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q"
    using lift_span[OF \<phi> sp] by simp
  finally have "F \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q = L \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> B \<cdot>\<^sub>a q" .
  then show "F \<cdot>\<^sub>a \<phi> = L \<cdot>\<^sub>a \<phi>"
    by (rule iso_cancel_right[OF N B_iso[OF st(1)], rotated -1])
      (use F \<phi> st lift_arr[OF \<phi>] agree_obj[OF FB] in simp_all)
qed

end

subsection \<open>Natural transformations\<close>

text \<open>
  A transformation \<open>\<theta> : F \<circ> A \<rightarrow> G \<circ> A\<close> is already one from \<open>F\<close> to \<open>G\<close>: the objects are the same,
  and naturality at \<open>\<phi>\<close> with span \<open>(q, t)\<close> follows from naturality at \<open>t\<close> and \<open>q\<close> after cancelling
  the isomorphism \<open>F (A q)\<close>.
\<close>

context span_criterion
begin

lemma nat_trans_descends:
  assumes N: "category N" and F: "is_functor F E N" and G: "is_functor G E N"
    and \<theta>: "nat_trans \<theta> (fcomp D F A) (fcomp D G A) D N"
  shows "nat_trans \<theta> F G E N"
proof -
  have \<theta>x: "\<theta> \<cdot> x \<in> Arr N" "src\<^bsub>N\<^esub> (\<theta> \<cdot> x) = F \<cdot>\<^sub>o x" "tgt\<^bsub>N\<^esub> (\<theta> \<cdot> x) = G \<cdot>\<^sub>o x" if "x \<in> Ob D" for x
    using nat_trans_arr[OF \<theta> that] nat_trans_src[OF \<theta> that] nat_trans_tgt[OF \<theta> that] that
    by simp_all
  have \<theta>f: "\<theta> \<cdot> tgt\<^bsub>D\<^esub> u \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a u) = G \<cdot>\<^sub>a (A \<cdot>\<^sub>a u) \<circ>\<^bsub>N\<^esub> \<theta> \<cdot> src\<^bsub>D\<^esub> u" if "u \<in> Arr D" for u
    using nat_trans_natural[OF \<theta> that] that by simp
  show ?thesis
  proof (rule nat_trans_intro)
    fix x assume "x \<in> Ob E"
    then show "\<theta> \<cdot> x \<in> Arr N" "src\<^bsub>N\<^esub> (\<theta> \<cdot> x) = F \<cdot>\<^sub>o x" "tgt\<^bsub>N\<^esub> (\<theta> \<cdot> x) = G \<cdot>\<^sub>o x"
      using \<theta>x by simp_all
  next
    fix \<phi> assume \<phi>: "\<phi> \<in> Arr E"
    obtain q t where sp: "is_span A W D E \<phi> q t"
      using \<phi> by (rule span_exists)
    note st = is_spanD[OF sp]
    have Fq: "iso N (F \<cdot>\<^sub>a (A \<cdot>\<^sub>a q))"
      using E F A_iso[OF st(1)] by (rule functor_iso)
    have "(\<theta> \<cdot> tgt\<^bsub>E\<^esub> \<phi> \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a \<phi>) \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a q)
        = (G \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> \<theta> \<cdot> src\<^bsub>E\<^esub> \<phi>) \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a q)"
    proof -
      have "(\<theta> \<cdot> tgt\<^bsub>E\<^esub> \<phi> \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a \<phi>) \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a q)
          = \<theta> \<cdot> tgt\<^bsub>E\<^esub> \<phi> \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (\<phi> \<circ>\<^bsub>E\<^esub> A \<cdot>\<^sub>a q)"
        using N F \<phi> st \<theta>x functor_comp[OF F A_arr[OF st(2)] \<phi>] by (simp add: cat_assoc)
      also have "\<dots> = \<theta> \<cdot> tgt\<^bsub>D\<^esub> t \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a t)"
        using is_span_eq[OF sp] st by simp
      also have "\<dots> = G \<cdot>\<^sub>a (A \<cdot>\<^sub>a t) \<circ>\<^bsub>N\<^esub> \<theta> \<cdot> src\<^bsub>D\<^esub> q"
        using \<theta>f[OF st(3)] st by simp
      also have "\<dots> = G \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> (G \<cdot>\<^sub>a (A \<cdot>\<^sub>a q) \<circ>\<^bsub>N\<^esub> \<theta> \<cdot> src\<^bsub>D\<^esub> q)"
        using D E N G \<phi> st \<theta>x is_span_eq[OF sp] functor_comp[OF G A_arr[OF st(2)] \<phi>]
        by (simp add: cat_assoc)
      also have "\<dots> = G \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> (\<theta> \<cdot> src\<^bsub>E\<^esub> \<phi> \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a q))"
        using \<theta>f[OF st(2)] st by simp
      also have "\<dots> = (G \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> \<theta> \<cdot> src\<^bsub>E\<^esub> \<phi>) \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a (A \<cdot>\<^sub>a q)"
        using D E N F G \<phi> st \<theta>x by (simp add: cat_assoc)
      finally show ?thesis .
    qed
    then show "\<theta> \<cdot> tgt\<^bsub>E\<^esub> \<phi> \<circ>\<^bsub>N\<^esub> F \<cdot>\<^sub>a \<phi> = G \<cdot>\<^sub>a \<phi> \<circ>\<^bsub>N\<^esub> \<theta> \<cdot> src\<^bsub>E\<^esub> \<phi>"
      by (rule iso_cancel_right[OF N Fq, rotated -1]) (use D E N F G \<phi> st \<theta>x in simp_all)
  qed
qed

end

subsection \<open>The criterion\<close>

theorem span_localization:
  assumes "category D" and "category E" and "is_functor A D E"
    and "identity_on_objects A D E"
    and "multiplicative W D"
    and "inverts A W E"
    and "has_spans A W D E"
    and "has_sections A W D"
  shows "strict_localization A W D E"
proof -
  interpret span_criterion A W D E
    using assms by unfold_locales
  have univ: "(\<exists>B'. is_functor B' E N \<and> agree D (fcomp D B' A) B) \<and>
      (\<forall>B' B''. is_functor B' E N \<longrightarrow> is_functor B'' E N \<longrightarrow>
        agree D (fcomp D B' A) B \<longrightarrow> agree D (fcomp D B'' A) B \<longrightarrow> agree E B' B'')"
    if N: "category N" and B: "is_functor B D N" and invB: "inverts B W N" for N B
  proof -
    interpret span_target A W D E N B
      using N B invB by unfold_locales
    have "agree E B' B''"
      if "is_functor B' E N" "is_functor B'' E N"
        "agree D (fcomp D B' A) B" "agree D (fcomp D B'' A) B" for B' B''
    proof (rule agreeI)
      fix x assume "x \<in> Ob E"
      then show "B' \<cdot>\<^sub>o x = B'' \<cdot>\<^sub>o x"
        using agree_obj[OF agree_lift[OF that(1,3)]] agree_obj[OF agree_lift[OF that(2,4)]]
        by simp
    next
      fix f assume "f \<in> Arr E"
      then show "B' \<cdot>\<^sub>a f = B'' \<cdot>\<^sub>a f"
        using agree_arr[OF agree_lift[OF that(1,3)]] agree_arr[OF agree_lift[OF that(2,4)]]
        by simp
    qed
    then show ?thesis
      using lift_functor lift_agree by blast
  qed
  have nat: "(\<exists>\<theta>'. nat_trans \<theta>' F G E N \<and> (\<forall>\<^sub>s x. x \<in> Ob D \<longrightarrow> \<theta>' \<cdot> (A \<cdot>\<^sub>o x) = \<theta> \<cdot> x)) \<and>
      (\<forall>\<theta>' \<theta>''. nat_trans \<theta>' F G E N \<longrightarrow> nat_trans \<theta>'' F G E N \<longrightarrow>
        (\<forall>\<^sub>s x. x \<in> Ob D \<longrightarrow> \<theta>' \<cdot> (A \<cdot>\<^sub>o x) = \<theta>'' \<cdot> (A \<cdot>\<^sub>o x)) \<longrightarrow>
        (\<forall>\<^sub>s y. y \<in> Ob E \<longrightarrow> \<theta>' \<cdot> y = \<theta>'' \<cdot> y))"
    if "category N" "is_functor F E N" "is_functor G E N"
      "nat_trans \<theta> (fcomp D F A) (fcomp D G A) D N" for N F G \<theta>
  proof -
    have "nat_trans \<theta> F G E N"
      using that by (rule nat_trans_descends)
    then show ?thesis
      by simp blast
  qed
  show ?thesis
    unfolding strict_localization_def using assms(3,6) univ nat by blast
qed

subsection \<open>The class of all inverted morphisms\<close>

text \<open>
  A localization at \<open>W\<close> is also the localization at every larger class that its functor inverts,
  and the largest such class is the class of all arrows that the functor inverts.
\<close>

lemma mem_inverted [simp]:
  "a \<in> \<lbrace>a. a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a)\<rbrace> \<longleftrightarrow> a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a)"
proof -
  have "dfn (\<lambda>a. a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a))"
    by dfn
  from Coll_iff[OF this] show ?thesis
    by (auto dest: mem_M)
qed

lemma inverts_inverted: "inverts A \<lbrace>a. a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a)\<rbrace> E"
  unfolding inverts_def by simp

lemma inverts_mono:
  assumes "inverts B W' N" and "\<And>w. w \<in> W \<Longrightarrow> w \<in> W'"
  shows "inverts B W N"
  using assms unfolding inverts_def by blast

lemma strict_localization_lift:
  assumes "strict_localization A W D E" and "category N" and "is_functor B D N"
    and "inverts B W N"
  obtains B' where "is_functor B' E N" and "agree D (fcomp D B' A) B"
  using assms unfolding strict_localization_def by blast

lemma strict_localization_mono:
  assumes loc: "strict_localization A W D E"
    and sub: "\<And>w. w \<in> W \<Longrightarrow> w \<in> W'"
    and inv: "inverts A W' E"
  shows "strict_localization A W' D E"
proof -
  have "inverts B W N" if "inverts B W' N" for B N
    using that sub by (rule inverts_mono)
  then show ?thesis
    using loc inv unfolding strict_localization_def by blast
qed

lemma strict_localization_at_inverted:
  assumes loc: "strict_localization A W D E" and W: "\<And>w. w \<in> W \<Longrightarrow> w \<in> Arr D"
  shows "strict_localization A \<lbrace>a. a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a)\<rbrace> D E"
proof (rule strict_localization_mono[OF loc])
  have invA: "inverts A W E"
    using loc unfolding strict_localization_def by blast
  show "w \<in> \<lbrace>a. a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a)\<rbrace>" if "w \<in> W" for w
    using that W invA unfolding inverts_def by (auto dest: mem_M)
  show "inverts A \<lbrace>a. a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a)\<rbrace> E"
    by (rule inverts_inverted)
qed

text \<open>
  A functor out of \<open>D\<close> that inverts \<open>W\<close> factors through the localization, so it inverts
  everything the localization functor inverts.
\<close>

lemma localization_inverts_all_inverted:
  assumes loc: "strict_localization A W D E" and E: "category E"
    and N: "category N" and B: "is_functor B D N" and invB: "inverts B W N"
  shows "inverts B \<lbrace>a. a \<in> Arr D \<and> iso E (A \<cdot>\<^sub>a a)\<rbrace> N"
proof -
  obtain B' where B': "is_functor B' E N" and ag: "agree D (fcomp D B' A) B"
    using loc N B invB by (rule strict_localization_lift)
  have "iso N (B \<cdot>\<^sub>a a)" if a: "a \<in> Arr D" and i: "iso E (A \<cdot>\<^sub>a a)" for a
  proof -
    have "B \<cdot>\<^sub>a a = B' \<cdot>\<^sub>a (A \<cdot>\<^sub>a a)"
      using agree_arr[OF ag a] a by simp
    then show ?thesis
      using functor_iso[OF E B' i] by simp
  qed
  then show ?thesis
    unfolding inverts_def by simp
qed

end
