section \<open>Categories, functors and natural transformations as classes\<close>

theory Category
  imports NBG.Library
begin

text \<open>
  A category is one class with six tagged components: objects, arrows, the source and target
  maps, the identity map and the composition map. It is small exactly when it is a set. The
  four maps are used only through application, so \<open>category C\<close> says that the objects and arrows
  of \<open>C\<close>, with \<open>src\<close>, \<open>tgt\<close>, \<open>id\<close> and \<open>\<circ>\<close> read off by application, form a category; whatever else
  the six classes contain is irrelevant.

  Hom-classes are not required to be sets. That is the separate hypothesis \<open>locally_small\<close>.
\<close>

subsection \<open>Categories\<close>

definition Ob :: "cls \<Rightarrow> cls"
  where "Ob C = cmp l0 C"

definition Arr :: "cls \<Rightarrow> cls"
  where "Arr C = cmp l1 C"

definition Src :: "cls \<Rightarrow> cls"
  where "Src C = cmp l2 C"

definition Tgt :: "cls \<Rightarrow> cls"
  where "Tgt C = cmp l3 C"

definition Idt :: "cls \<Rightarrow> cls"
  where "Idt C = cmp l4 C"

definition Cmp :: "cls \<Rightarrow> cls"
  where "Cmp C = cmp l5 C"

definition mkcat :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "mkcat obs arrs s t i c = tag l0 obs \<union> tag l1 arrs \<union> tag l2 s \<union> tag l3 t \<union> tag l4 i \<union> tag l5 c"

definition src :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (\<open>src\<^bsub>_\<^esub>\<close>)
  where "src\<^bsub>C\<^esub> f = Src C \<cdot> f"

definition tgt :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (\<open>tgt\<^bsub>_\<^esub>\<close>)
  where "tgt\<^bsub>C\<^esub> f = Tgt C \<cdot> f"

definition idt :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (\<open>id\<^bsub>_\<^esub>\<close>)
  where "id\<^bsub>C\<^esub> x = Idt C \<cdot> x"

definition ccomp :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"  (\<open>(\<open>notation=\<open>infix \<circ>\<close>\<close>_ \<circ>\<^bsub>_\<^esub>/ _)\<close> [55, 0, 56] 55)
  where "g \<circ>\<^bsub>C\<^esub> f = Cmp C \<cdot> \<langle>g, f\<rangle>"

definition Hom :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Hom C x y = \<lbrace>f. f \<in> Arr C \<and> src\<^bsub>C\<^esub> f = x \<and> tgt\<^bsub>C\<^esub> f = y\<rbrace>"

definition category :: "cls \<Rightarrow> bool"
  where "category C \<longleftrightarrow>
    (\<forall>\<^sub>s f. f \<in> Arr C \<longrightarrow> src\<^bsub>C\<^esub> f \<in> Ob C \<and> tgt\<^bsub>C\<^esub> f \<in> Ob C) \<and>
    (\<forall>\<^sub>s x. x \<in> Ob C \<longrightarrow> id\<^bsub>C\<^esub> x \<in> Arr C \<and> src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> x) = x \<and> tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> x) = x) \<and>
    (\<forall>\<^sub>s f g. f \<in> Arr C \<longrightarrow> g \<in> Arr C \<longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<longrightarrow>
      g \<circ>\<^bsub>C\<^esub> f \<in> Arr C \<and> src\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = src\<^bsub>C\<^esub> f \<and> tgt\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = tgt\<^bsub>C\<^esub> g) \<and>
    (\<forall>\<^sub>s f. f \<in> Arr C \<longrightarrow> f \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f) = f \<and> id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> f = f) \<and>
    (\<forall>\<^sub>s f g h. f \<in> Arr C \<longrightarrow> g \<in> Arr C \<longrightarrow> h \<in> Arr C \<longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<longrightarrow> src\<^bsub>C\<^esub> h = tgt\<^bsub>C\<^esub> g \<longrightarrow>
      h \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = (h \<circ>\<^bsub>C\<^esub> g) \<circ>\<^bsub>C\<^esub> f)"

definition locally_small :: "cls \<Rightarrow> bool"
  where "locally_small C \<longleftrightarrow> (\<forall>\<^sub>s x y. x \<in> Ob C \<longrightarrow> y \<in> Ob C \<longrightarrow> M (Hom C x y))"

definition iso :: "cls \<Rightarrow> cls \<Rightarrow> bool"
  where "iso C f \<longleftrightarrow> f \<in> Arr C \<and>
    (\<exists>\<^sub>s g. g \<in> Arr C \<and> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<and> tgt\<^bsub>C\<^esub> g = src\<^bsub>C\<^esub> f \<and>
      g \<circ>\<^bsub>C\<^esub> f = id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f) \<and> f \<circ>\<^bsub>C\<^esub> g = id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f))"

subsection \<open>Functors\<close>

text \<open>
  A functor is one class with two tagged components, the object map and the arrow map, again
  used only through application: \<open>F \<cdot>\<^sub>o x\<close> and \<open>F \<cdot>\<^sub>a f\<close>.
\<close>

definition FOb :: "cls \<Rightarrow> cls"
  where "FOb F = cmp l0 F"

definition FArr :: "cls \<Rightarrow> cls"
  where "FArr F = cmp l1 F"

definition mkfun :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "mkfun on_obs on_arrs = tag l0 on_obs \<union> tag l1 on_arrs"

definition obj :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (infixl \<open>\<cdot>\<^sub>o\<close> 90)
  where "F \<cdot>\<^sub>o x = FOb F \<cdot> x"

definition arr :: "cls \<Rightarrow> cls \<Rightarrow> cls"  (infixl \<open>\<cdot>\<^sub>a\<close> 90)
  where "F \<cdot>\<^sub>a f = FArr F \<cdot> f"

definition is_functor :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "is_functor F C D \<longleftrightarrow>
    (\<forall>\<^sub>s x. x \<in> Ob C \<longrightarrow> F \<cdot>\<^sub>o x \<in> Ob D) \<and>
    (\<forall>\<^sub>s f. f \<in> Arr C \<longrightarrow>
      F \<cdot>\<^sub>a f \<in> Arr D \<and> src\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f) = F \<cdot>\<^sub>o src\<^bsub>C\<^esub> f \<and> tgt\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f) = F \<cdot>\<^sub>o tgt\<^bsub>C\<^esub> f) \<and>
    (\<forall>\<^sub>s x. x \<in> Ob C \<longrightarrow> F \<cdot>\<^sub>a id\<^bsub>C\<^esub> x = id\<^bsub>D\<^esub> (F \<cdot>\<^sub>o x)) \<and>
    (\<forall>\<^sub>s f g. f \<in> Arr C \<longrightarrow> g \<in> Arr C \<longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<longrightarrow>
      F \<cdot>\<^sub>a (g \<circ>\<^bsub>C\<^esub> f) = F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f)"

text \<open>The identity functor of \<open>C\<close>, and \<open>G\<close> after \<open>F\<close> for a functor \<open>F\<close> out of \<open>C\<close>.\<close>

definition idf :: "cls \<Rightarrow> cls"
  where "idf C = mkfun (\<lambda>x\<in>Ob C. x) (\<lambda>f\<in>Arr C. f)"

definition fcomp :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "fcomp C G F = mkfun (\<lambda>x\<in>Ob C. G \<cdot>\<^sub>o (F \<cdot>\<^sub>o x)) (\<lambda>f\<in>Arr C. G \<cdot>\<^sub>a (F \<cdot>\<^sub>a f))"

text \<open>
  Two classes can act as the same functor and differ as classes. Where functors are themselves
  the arrows of a category, each needs one representative: \<open>strict_functor\<close> singles out the
  functor that is exactly its two maps and nothing else.
\<close>

definition strict_functor :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "strict_functor F C D \<longleftrightarrow>
    is_functor F C D \<and> F = mkfun (\<lambda>x\<in>Ob C. F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. F \<cdot>\<^sub>a f)"

text \<open>Two functors out of \<open>C\<close> that agree on its objects and arrows.\<close>

definition agree :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "agree C F G \<longleftrightarrow>
    (\<forall>\<^sub>s x. x \<in> Ob C \<longrightarrow> F \<cdot>\<^sub>o x = G \<cdot>\<^sub>o x) \<and> (\<forall>\<^sub>s f. f \<in> Arr C \<longrightarrow> F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f)"

subsection \<open>Natural transformations\<close>

text \<open>A natural transformation is a class of components \<open>\<theta> \<cdot> x\<close>, one for each object \<open>x\<close>.\<close>

definition nat_trans :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "nat_trans \<theta> F G C D \<longleftrightarrow>
    (\<forall>\<^sub>s x. x \<in> Ob C \<longrightarrow>
      \<theta> \<cdot> x \<in> Arr D \<and> src\<^bsub>D\<^esub> (\<theta> \<cdot> x) = F \<cdot>\<^sub>o x \<and> tgt\<^bsub>D\<^esub> (\<theta> \<cdot> x) = G \<cdot>\<^sub>o x) \<and>
    (\<forall>\<^sub>s f. f \<in> Arr C \<longrightarrow> \<theta> \<cdot> tgt\<^bsub>C\<^esub> f \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a f \<circ>\<^bsub>D\<^esub> \<theta> \<cdot> src\<^bsub>C\<^esub> f)"

subsection \<open>Localization\<close>

text \<open>
  \<open>inverts B W N\<close>: the functor \<open>B\<close> into \<open>N\<close> sends every arrow in the class \<open>W\<close> to an isomorphism.

  \<open>strict_localization A W D E\<close>: the functor \<open>A : D \<rightarrow> E\<close> inverts \<open>W\<close>, and it is universal with
  that property on the nose. Every functor \<open>B : D \<rightarrow> N\<close> that inverts \<open>W\<close> is \<open>B' \<circ> A\<close> for a functor
  \<open>B' : E \<rightarrow> N\<close>, any two such \<open>B'\<close> agree, and natural transformations between functors out of \<open>E\<close>
  are the same thing as natural transformations between their composites with \<open>A\<close>. The
  quantifiers over \<open>N\<close>, \<open>B\<close>, \<open>B'\<close> and the transformations range over classes, so this is one
  statement of NBG about \<open>A\<close>, \<open>W\<close>, \<open>D\<close> and \<open>E\<close>.

  In other words, composition with \<open>A\<close> is an isomorphism from the functors \<open>E \<rightarrow> N\<close> to the
  functors \<open>D \<rightarrow> N\<close> that invert \<open>W\<close>, for every \<open>N\<close>. That is the universal property of the
  category of fractions \<open>D[W⁻¹]\<close>, and it implies the usual one, where the comparison is only
  asked to be an equivalence.
\<close>

definition inverts :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "inverts B W N \<longleftrightarrow> (\<forall>\<^sub>s w. w \<in> W \<longrightarrow> iso N (B \<cdot>\<^sub>a w))"

definition strict_localization :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> bool"
  where "strict_localization A W D E \<longleftrightarrow>
    is_functor A D E \<and> inverts A W E \<and>
    (\<forall>N B. category N \<longrightarrow> is_functor B D N \<longrightarrow> inverts B W N \<longrightarrow>
      (\<exists>B'. is_functor B' E N \<and> agree D (fcomp D B' A) B) \<and>
      (\<forall>B' B''. is_functor B' E N \<longrightarrow> is_functor B'' E N \<longrightarrow>
        agree D (fcomp D B' A) B \<longrightarrow> agree D (fcomp D B'' A) B \<longrightarrow> agree E B' B'')) \<and>
    (\<forall>N F G \<theta>. category N \<longrightarrow> is_functor F E N \<longrightarrow> is_functor G E N \<longrightarrow>
      nat_trans \<theta> (fcomp D F A) (fcomp D G A) D N \<longrightarrow>
      (\<exists>\<theta>'. nat_trans \<theta>' F G E N \<and> (\<forall>\<^sub>s x. x \<in> Ob D \<longrightarrow> \<theta>' \<cdot> (A \<cdot>\<^sub>o x) = \<theta> \<cdot> x)) \<and>
      (\<forall>\<theta>' \<theta>''. nat_trans \<theta>' F G E N \<longrightarrow> nat_trans \<theta>'' F G E N \<longrightarrow>
        (\<forall>\<^sub>s x. x \<in> Ob D \<longrightarrow> \<theta>' \<cdot> (A \<cdot>\<^sub>o x) = \<theta>'' \<cdot> (A \<cdot>\<^sub>o x)) \<longrightarrow>
        (\<forall>\<^sub>s y. y \<in> Ob E \<longrightarrow> \<theta>' \<cdot> y = \<theta>'' \<cdot> y)))"

subsection \<open>Class existence for this vocabulary\<close>

text \<open>
  One rule for each operation and predicate above, so that comprehensions may mention them.
  \<open>strict_localization\<close> quantifies over classes and has no rule: it can be stated, but no class
  can be defined by it.
\<close>

lemma dcls_Ob [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. Ob (T x))" unfolding Ob_def by dfn
lemma dfun_Ob [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. Ob (f x))" unfolding Ob_def by dfn
lemma dcls_Arr [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. Arr (T x))" unfolding Arr_def by dfn
lemma dfun_Arr [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. Arr (f x))" unfolding Arr_def by dfn
lemma dcls_Src [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. Src (T x))" unfolding Src_def by dfn
lemma dfun_Src [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. Src (f x))" unfolding Src_def by dfn
lemma dcls_Tgt [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. Tgt (T x))" unfolding Tgt_def by dfn
lemma dfun_Tgt [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. Tgt (f x))" unfolding Tgt_def by dfn
lemma dcls_Idt [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. Idt (T x))" unfolding Idt_def by dfn
lemma dfun_Idt [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. Idt (f x))" unfolding Idt_def by dfn
lemma dcls_Cmp [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. Cmp (T x))" unfolding Cmp_def by dfn
lemma dfun_Cmp [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. Cmp (f x))" unfolding Cmp_def by dfn

lemma dcls_mkcat [dfn_rules]:
  "dcls A \<Longrightarrow> dcls B \<Longrightarrow> dcls S \<Longrightarrow> dcls T \<Longrightarrow> dcls I \<Longrightarrow> dcls K \<Longrightarrow>
    dcls (\<lambda>x. mkcat (A x) (B x) (S x) (T x) (I x) (K x))"
  unfolding mkcat_def by dfn

lemma dfun_mkcat [dfn_rules]:
  "dfun A \<Longrightarrow> dfun B \<Longrightarrow> dfun S \<Longrightarrow> dfun T \<Longrightarrow> dfun I \<Longrightarrow> dfun K \<Longrightarrow>
    dfun (\<lambda>x. mkcat (A x) (B x) (S x) (T x) (I x) (K x))"
  unfolding mkcat_def by dfn

lemma dfun_src [dfn_rules]: "dcls T \<Longrightarrow> dcls S \<Longrightarrow> dfun (\<lambda>x. src\<^bsub>T x\<^esub> (S x))"
  unfolding src_def by dfn

lemma dfun_tgt [dfn_rules]: "dcls T \<Longrightarrow> dcls S \<Longrightarrow> dfun (\<lambda>x. tgt\<^bsub>T x\<^esub> (S x))"
  unfolding tgt_def by dfn

lemma dfun_idt [dfn_rules]: "dcls T \<Longrightarrow> dcls S \<Longrightarrow> dfun (\<lambda>x. id\<^bsub>T x\<^esub> (S x))"
  unfolding idt_def by dfn

lemma dfun_ccomp [dfn_rules]: "dcls T \<Longrightarrow> dcls G \<Longrightarrow> dcls F \<Longrightarrow> dfun (\<lambda>x. G x \<circ>\<^bsub>T x\<^esub> F x)"
  unfolding ccomp_def by dfn

lemma dcls_Hom [dfn_rules]: "dcls T \<Longrightarrow> dcls A \<Longrightarrow> dcls B \<Longrightarrow> dcls (\<lambda>x. Hom (T x) (A x) (B x))"
  unfolding Hom_def by dfn

lemma dfn_category [dfn_rules]: "dcls T \<Longrightarrow> dfn (\<lambda>x. category (T x))"
  unfolding category_def by dfn

lemma dfn_iso [dfn_rules]: "dcls T \<Longrightarrow> dfun f \<Longrightarrow> dfn (\<lambda>x. iso (T x) (f x))"
  unfolding iso_def by dfn

lemma dcls_FOb [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. FOb (T x))" unfolding FOb_def by dfn
lemma dfun_FOb [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. FOb (f x))" unfolding FOb_def by dfn
lemma dcls_FArr [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. FArr (T x))" unfolding FArr_def by dfn
lemma dfun_FArr [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. FArr (f x))" unfolding FArr_def by dfn

lemma dcls_mkfun [dfn_rules]: "dcls S \<Longrightarrow> dcls T \<Longrightarrow> dcls (\<lambda>x. mkfun (S x) (T x))"
  unfolding mkfun_def by dfn

lemma dfun_mkfun [dfn_rules]: "dfun f \<Longrightarrow> dfun g \<Longrightarrow> dfun (\<lambda>x. mkfun (f x) (g x))"
  unfolding mkfun_def by dfn

lemma dfun_obj [dfn_rules]: "dcls F \<Longrightarrow> dcls S \<Longrightarrow> dfun (\<lambda>x. F x \<cdot>\<^sub>o S x)"
  unfolding obj_def by dfn

lemma dfun_arr [dfn_rules]: "dcls F \<Longrightarrow> dcls S \<Longrightarrow> dfun (\<lambda>x. F x \<cdot>\<^sub>a S x)"
  unfolding arr_def by dfn

lemma dfn_is_functor [dfn_rules]:
  "dcls F \<Longrightarrow> dcls C \<Longrightarrow> dcls D \<Longrightarrow> dfn (\<lambda>x. is_functor (F x) (C x) (D x))"
  unfolding is_functor_def by dfn

lemma dcls_idf [dfn_rules]: "dcls T \<Longrightarrow> dcls (\<lambda>x. idf (T x))" unfolding idf_def by dfn
lemma dfun_idf [dfn_rules]: "dfun f \<Longrightarrow> dfun (\<lambda>x. idf (f x))" unfolding idf_def by dfn

lemma dcls_fcomp [dfn_rules]:
  "dcls C \<Longrightarrow> dcls G \<Longrightarrow> dcls F \<Longrightarrow> dcls (\<lambda>x. fcomp (C x) (G x) (F x))"
  unfolding fcomp_def by dfn

lemma dfun_fcomp [dfn_rules]:
  "dfun C \<Longrightarrow> dcls G \<Longrightarrow> dcls F \<Longrightarrow> dfun (\<lambda>x. fcomp (C x) (G x) (F x))"
  unfolding fcomp_def by dfn

lemma dfn_strict_functor [dfn_rules]:
  "dcls F \<Longrightarrow> dcls C \<Longrightarrow> dcls D \<Longrightarrow> dfn (\<lambda>x. strict_functor (F x) (C x) (D x))"
  unfolding strict_functor_def by dfn

lemma dfn_agree [dfn_rules]:
  "dcls C \<Longrightarrow> dcls F \<Longrightarrow> dcls G \<Longrightarrow> dfn (\<lambda>x. agree (C x) (F x) (G x))"
  unfolding agree_def by dfn

lemma dfn_nat_trans [dfn_rules]:
  "dcls \<theta> \<Longrightarrow> dcls F \<Longrightarrow> dcls G \<Longrightarrow> dcls C \<Longrightarrow> dcls D \<Longrightarrow>
    dfn (\<lambda>x. nat_trans (\<theta> x) (F x) (G x) (C x) (D x))"
  unfolding nat_trans_def by dfn

lemma dfn_inverts [dfn_rules]:
  "dcls B \<Longrightarrow> dcls W \<Longrightarrow> dcls N \<Longrightarrow> dfn (\<lambda>x. inverts (B x) (W x) (N x))"
  unfolding inverts_def by dfn

subsection \<open>Reading a structure\<close>

text \<open>The components of \<open>mkcat\<close> and \<open>mkfun\<close>, and the values of the maps read off them.\<close>

lemma Ob_mkcat [simp]: "Ob (mkcat obs arrs s t i c) = obs"
  by (simp add: Ob_def mkcat_def)

lemma Arr_mkcat [simp]: "Arr (mkcat obs arrs s t i c) = arrs"
  by (simp add: Arr_def mkcat_def)

lemma Src_mkcat [simp]: "Src (mkcat obs arrs s t i c) = s"
  by (simp add: Src_def mkcat_def)

lemma Tgt_mkcat [simp]: "Tgt (mkcat obs arrs s t i c) = t"
  by (simp add: Tgt_def mkcat_def)

lemma Idt_mkcat [simp]: "Idt (mkcat obs arrs s t i c) = i"
  by (simp add: Idt_def mkcat_def)

lemma Cmp_mkcat [simp]: "Cmp (mkcat obs arrs s t i c) = c"
  by (simp add: Cmp_def mkcat_def)

lemma FOb_mkfun [simp]: "FOb (mkfun a b) = a"
  by (simp add: FOb_def mkfun_def)

lemma FArr_mkfun [simp]: "FArr (mkfun a b) = b"
  by (simp add: FArr_def mkfun_def)

lemma M_src [simp]: "M (src\<^bsub>C\<^esub> f)" by (simp add: src_def)
lemma M_tgt [simp]: "M (tgt\<^bsub>C\<^esub> f)" by (simp add: tgt_def)
lemma M_idt [simp]: "M (id\<^bsub>C\<^esub> x)" by (simp add: idt_def)
lemma M_ccomp [simp]: "M (g \<circ>\<^bsub>C\<^esub> f)" by (simp add: ccomp_def)
lemma M_obj [simp]: "M (F \<cdot>\<^sub>o x)" by (simp add: obj_def)
lemma M_arr [simp]: "M (F \<cdot>\<^sub>a f)" by (simp add: arr_def)

lemma idf_obj [simp]: "x \<in> Ob C \<Longrightarrow> idf C \<cdot>\<^sub>o x = x"
  by (simp add: idf_def obj_def mem_M)

lemma idf_arr [simp]: "f \<in> Arr C \<Longrightarrow> idf C \<cdot>\<^sub>a f = f"
  by (simp add: idf_def arr_def mem_M)

lemma fcomp_obj [simp]: "x \<in> Ob C \<Longrightarrow> fcomp C G F \<cdot>\<^sub>o x = G \<cdot>\<^sub>o (F \<cdot>\<^sub>o x)"
  by (simp add: fcomp_def obj_def[of "mkfun _ _"])

lemma fcomp_arr [simp]: "f \<in> Arr C \<Longrightarrow> fcomp C G F \<cdot>\<^sub>a f = G \<cdot>\<^sub>a (F \<cdot>\<^sub>a f)"
  by (simp add: fcomp_def arr_def[of "mkfun _ _"])

text \<open>The identity functor and a composite are canonical: exactly their two maps.\<close>

lemma idf_canonical: "idf C = mkfun (\<lambda>x\<in>Ob C. idf C \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. idf C \<cdot>\<^sub>a f)"
  by (simp cong: Lam_cong) (simp add: idf_def)

lemma fcomp_canonical:
  "fcomp C G F = mkfun (\<lambda>x\<in>Ob C. fcomp C G F \<cdot>\<^sub>o x) (\<lambda>f\<in>Arr C. fcomp C G F \<cdot>\<^sub>a f)"
  by (simp cong: Lam_cong) (simp add: fcomp_def)

lemma src_mkcat [simp]: "src\<^bsub>mkcat obs arrs s t i c\<^esub> f = s \<cdot> f" by (simp add: src_def)
lemma tgt_mkcat [simp]: "tgt\<^bsub>mkcat obs arrs s t i c\<^esub> f = t \<cdot> f" by (simp add: tgt_def)
lemma idt_mkcat [simp]: "id\<^bsub>mkcat obs arrs s t i c\<^esub> x = i \<cdot> x" by (simp add: idt_def)
lemma ccomp_mkcat [simp]: "g \<circ>\<^bsub>mkcat obs arrs s t i c\<^esub> f = c \<cdot> \<langle>g, f\<rangle>" by (simp add: ccomp_def)
lemma obj_mkfun [simp]: "mkfun a b \<cdot>\<^sub>o x = a \<cdot> x" by (simp add: obj_def)
lemma arr_mkfun [simp]: "mkfun a b \<cdot>\<^sub>a f = b \<cdot> f" by (simp add: arr_def)

lemma mem_Hom [simp]: "f \<in> Hom C x y \<longleftrightarrow> f \<in> Arr C \<and> src\<^bsub>C\<^esub> f = x \<and> tgt\<^bsub>C\<^esub> f = y"
  by (auto simp: Hom_def mem_M)

subsection \<open>The axioms as rules\<close>

text \<open>
  The definitions quantify over sets. A member of a class is a set, so the rules below ask only
  for membership.
\<close>

lemma categoryI:
  assumes "\<And>f. f \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> f \<in> Ob C"
    and "\<And>f. f \<in> Arr C \<Longrightarrow> tgt\<^bsub>C\<^esub> f \<in> Ob C"
    and "\<And>x. x \<in> Ob C \<Longrightarrow> id\<^bsub>C\<^esub> x \<in> Arr C"
    and "\<And>x. x \<in> Ob C \<Longrightarrow> src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> x) = x"
    and "\<And>x. x \<in> Ob C \<Longrightarrow> tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> x) = x"
    and "\<And>f g. f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow> g \<circ>\<^bsub>C\<^esub> f \<in> Arr C"
    and "\<And>f g. f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow> src\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = src\<^bsub>C\<^esub> f"
    and "\<And>f g. f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow> tgt\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = tgt\<^bsub>C\<^esub> g"
    and "\<And>f. f \<in> Arr C \<Longrightarrow> f \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f) = f"
    and "\<And>f. f \<in> Arr C \<Longrightarrow> id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> f = f"
    and "\<And>f g h. f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> h \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow>
      src\<^bsub>C\<^esub> h = tgt\<^bsub>C\<^esub> g \<Longrightarrow> h \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = (h \<circ>\<^bsub>C\<^esub> g) \<circ>\<^bsub>C\<^esub> f"
  shows "category C"
  unfolding category_def using assms by simp

lemma cat_src [simp]: "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> f \<in> Ob C"
  unfolding category_def by (simp add: mem_M)

lemma cat_tgt [simp]: "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> tgt\<^bsub>C\<^esub> f \<in> Ob C"
  unfolding category_def by (simp add: mem_M)

lemma cat_id [simp]: "category C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> id\<^bsub>C\<^esub> x \<in> Arr C"
  unfolding category_def by (simp add: mem_M)

lemma cat_src_id [simp]: "category C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> src\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> x) = x"
  unfolding category_def by (simp add: mem_M)

lemma cat_tgt_id [simp]: "category C \<Longrightarrow> x \<in> Ob C \<Longrightarrow> tgt\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> x) = x"
  unfolding category_def by (simp add: mem_M)

lemma cat_comp [simp]:
  "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow> g \<circ>\<^bsub>C\<^esub> f \<in> Arr C"
  unfolding category_def by (simp add: mem_M)

lemma cat_src_comp [simp]:
  "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow> src\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = src\<^bsub>C\<^esub> f"
  unfolding category_def by (simp add: mem_M)

lemma cat_tgt_comp [simp]:
  "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow> tgt\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = tgt\<^bsub>C\<^esub> g"
  unfolding category_def by (simp add: mem_M)

lemma cat_id_right [simp]: "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> f \<circ>\<^bsub>C\<^esub> id\<^bsub>C\<^esub> (src\<^bsub>C\<^esub> f) = f"
  unfolding category_def by (simp add: mem_M)

lemma cat_id_left [simp]: "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> id\<^bsub>C\<^esub> (tgt\<^bsub>C\<^esub> f) \<circ>\<^bsub>C\<^esub> f = f"
  unfolding category_def by (simp add: mem_M)

lemma cat_assoc:
  "category C \<Longrightarrow> f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> h \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow>
    src\<^bsub>C\<^esub> h = tgt\<^bsub>C\<^esub> g \<Longrightarrow> h \<circ>\<^bsub>C\<^esub> (g \<circ>\<^bsub>C\<^esub> f) = (h \<circ>\<^bsub>C\<^esub> g) \<circ>\<^bsub>C\<^esub> f"
  unfolding category_def by (simp add: mem_M)

lemma is_functorI:
  assumes "\<And>x. x \<in> Ob C \<Longrightarrow> F \<cdot>\<^sub>o x \<in> Ob D"
    and "\<And>f. f \<in> Arr C \<Longrightarrow> F \<cdot>\<^sub>a f \<in> Arr D"
    and "\<And>f. f \<in> Arr C \<Longrightarrow> src\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f) = F \<cdot>\<^sub>o src\<^bsub>C\<^esub> f"
    and "\<And>f. f \<in> Arr C \<Longrightarrow> tgt\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f) = F \<cdot>\<^sub>o tgt\<^bsub>C\<^esub> f"
    and "\<And>x. x \<in> Ob C \<Longrightarrow> F \<cdot>\<^sub>a id\<^bsub>C\<^esub> x = id\<^bsub>D\<^esub> (F \<cdot>\<^sub>o x)"
    and "\<And>f g. f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow>
      F \<cdot>\<^sub>a (g \<circ>\<^bsub>C\<^esub> f) = F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f"
  shows "is_functor F C D"
  unfolding is_functor_def using assms by simp

lemma functor_obj [simp]: "is_functor F C D \<Longrightarrow> x \<in> Ob C \<Longrightarrow> F \<cdot>\<^sub>o x \<in> Ob D"
  unfolding is_functor_def by (simp add: mem_M)

lemma functor_arr [simp]: "is_functor F C D \<Longrightarrow> f \<in> Arr C \<Longrightarrow> F \<cdot>\<^sub>a f \<in> Arr D"
  unfolding is_functor_def by (simp add: mem_M)

lemma functor_src [simp]:
  "is_functor F C D \<Longrightarrow> f \<in> Arr C \<Longrightarrow> src\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f) = F \<cdot>\<^sub>o src\<^bsub>C\<^esub> f"
  unfolding is_functor_def by (simp add: mem_M)

lemma functor_tgt [simp]:
  "is_functor F C D \<Longrightarrow> f \<in> Arr C \<Longrightarrow> tgt\<^bsub>D\<^esub> (F \<cdot>\<^sub>a f) = F \<cdot>\<^sub>o tgt\<^bsub>C\<^esub> f"
  unfolding is_functor_def by (simp add: mem_M)

lemma functor_id [simp]:
  "is_functor F C D \<Longrightarrow> x \<in> Ob C \<Longrightarrow> F \<cdot>\<^sub>a id\<^bsub>C\<^esub> x = id\<^bsub>D\<^esub> (F \<cdot>\<^sub>o x)"
  unfolding is_functor_def by (simp add: mem_M)

lemma functor_comp:
  "is_functor F C D \<Longrightarrow> f \<in> Arr C \<Longrightarrow> g \<in> Arr C \<Longrightarrow> src\<^bsub>C\<^esub> g = tgt\<^bsub>C\<^esub> f \<Longrightarrow>
    F \<cdot>\<^sub>a (g \<circ>\<^bsub>C\<^esub> f) = F \<cdot>\<^sub>a g \<circ>\<^bsub>D\<^esub> F \<cdot>\<^sub>a f"
  unfolding is_functor_def by (simp add: mem_M)

end