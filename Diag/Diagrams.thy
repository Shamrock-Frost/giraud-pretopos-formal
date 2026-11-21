section \<open>Small diagrams in a category, and small presheaves on it\<close>

theory Diagrams
  imports Cat.Final Cat.Localization
begin

text \<open>
  \<open>C\<close> is a locally small category, possibly a proper class.

  \<open>Diag C\<close> is the category of small diagrams in \<open>C\<close>. An object is a pair \<open>\<langle>J, F\<rangle>\<close> of a small
  category \<open>J\<close> and a functor \<open>F : J \<rightarrow> C\<close>; both are sets. A morphism \<open>\<langle>J, F\<rangle> \<rightarrow> \<langle>K, G\<rangle>\<close> is a functor
  \<open>p : J \<rightarrow> K\<close> with a natural transformation \<open>\<alpha> : F \<Rightarrow> G \<circ> p\<close>.

  \<open>PSh C\<close> stands for the category of small presheaves on \<open>C\<close>. A small presheaf on a proper class
  is itself a proper class, so the small presheaves do not form a class and the category cannot
  be defined in NBG as it is in the note. What can be defined is the category with the same
  objects as \<open>Diag C\<close>, the diagram \<open>\<langle>J, F\<rangle>\<close> standing for the presheaf \<open>colim\<^sub>j y(F j)\<close>, and with
  morphisms given by the formula
    \<open>Hom(colim y F, colim y G) = lim\<^sub>j colim\<^sub>k Hom(F j, G k)\<close>.
  So a morphism \<open>\<langle>J, F\<rangle> \<rightarrow> \<langle>K, G\<rangle>\<close> of \<open>PSh C\<close> is a family \<open>\<phi>\<close>, indexed by the objects \<open>j\<close> of \<open>J\<close>, of
  connected components \<open>\<phi> \<cdot> j\<close> of the comma category \<open>(F j \<down> G)\<close>, compatible with the arrows of
  \<open>J\<close>. Local smallness of \<open>C\<close> makes each component a set.

  \<open>colim_functor C : Diag C \<rightarrow> PSh C\<close> is the functor called \<open>A\<close> in the note. It is the identity on
  objects and sends \<open>(p, \<alpha>)\<close> to the family of components of the \<open>\<langle>p j, \<alpha>\<^sub>j\<rangle>\<close>.

  \<open>W0 C\<close> is the class of morphisms \<open>(q, id) : \<langle>J', F \<circ> q\<rangle> \<rightarrow> \<langle>J, F\<rangle>\<close> of \<open>Diag C\<close> with \<open>q\<close> final.
\<close>

subsection \<open>Reading objects and arrows\<close>

text \<open>An object \<open>X = \<langle>J, F\<rangle>\<close>: its index category and its diagram.\<close>

definition ix :: "cls \<Rightarrow> cls"
  where "ix X = pfst X"

definition dg :: "cls \<Rightarrow> cls"
  where "dg X = psnd X"

text \<open>
  An arrow of either category is \<open>\<langle>\<langle>X, Y\<rangle>, m\<rangle>\<close>, with source \<open>X\<close>, target \<open>Y\<close> and body \<open>m\<close>. In
  \<open>Diag C\<close> the body is \<open>\<langle>p, \<alpha>\<rangle>\<close>; in \<open>PSh C\<close> it is the family \<open>\<phi>\<close>.
\<close>

definition asrc :: "cls \<Rightarrow> cls"
  where "asrc a = pfst (pfst a)"

definition atgt :: "cls \<Rightarrow> cls"
  where "atgt a = psnd (pfst a)"

definition body :: "cls \<Rightarrow> cls"
  where "body a = psnd a"

definition afun :: "cls \<Rightarrow> cls"
  where "afun a = pfst (body a)"

definition anat :: "cls \<Rightarrow> cls"
  where "anat a = psnd (body a)"

subsection \<open>The category of small diagrams\<close>

definition DOb :: "cls \<Rightarrow> cls"
  where "DOb C = \<lbrace>X. \<exists>\<^sub>s J F. X = \<langle>J, F\<rangle> \<and> category J \<and> is_functor F J C\<rbrace>"

definition DArr :: "cls \<Rightarrow> cls"
  where "DArr C =
    \<lbrace>a. \<exists>\<^sub>s X Y p \<alpha>. a = \<langle>\<langle>X, Y\<rangle>, \<langle>p, \<alpha>\<rangle>\<rangle> \<and> X \<in> DOb C \<and> Y \<in> DOb C \<and>
      strict_functor p (ix X) (ix Y) \<and>
      \<alpha> = (\<lambda>j\<in>Ob (ix X). \<alpha> \<cdot> j) \<and>
      (\<forall>\<^sub>s j. j \<in> Ob (ix X) \<longrightarrow>
        \<alpha> \<cdot> j \<in> Arr C \<and> src\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg X \<cdot>\<^sub>o j \<and> tgt\<^bsub>C\<^esub> (\<alpha> \<cdot> j) = dg Y \<cdot>\<^sub>o (p \<cdot>\<^sub>o j)) \<and>
      (\<forall>\<^sub>s u. u \<in> Arr (ix X) \<longrightarrow>
        \<alpha> \<cdot> tgt\<^bsub>ix X\<^esub> u \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u = dg Y \<cdot>\<^sub>a (p \<cdot>\<^sub>a u) \<circ>\<^bsub>C\<^esub> \<alpha> \<cdot> src\<^bsub>ix X\<^esub> u)\<rbrace>"

definition Did :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Did C X = \<langle>\<langle>X, X\<rangle>, \<langle>idf (ix X), \<lambda>j\<in>Ob (ix X). id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j)\<rangle>\<rangle>"

text \<open>\<open>Dcomp C b a\<close>: the composite \<open>b\<close> after \<open>a\<close>, that is \<open>(p', \<alpha>') \<circ> (p, \<alpha>) = (p' \<circ> p, \<alpha>'p \<circ> \<alpha>)\<close>.\<close>

definition Dcomp :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Dcomp C b a =
    \<langle>\<langle>asrc a, atgt b\<rangle>,
      \<langle>fcomp (ix (asrc a)) (afun b) (afun a),
        \<lambda>j\<in>Ob (ix (asrc a)). anat b \<cdot> (afun a \<cdot>\<^sub>o j) \<circ>\<^bsub>C\<^esub> anat a \<cdot> j\<rangle>\<rangle>"

definition Diag :: "cls \<Rightarrow> cls"
  where "Diag C =
    mkcat (DOb C) (DArr C) (\<lambda>a\<in>DArr C. asrc a) (\<lambda>a\<in>DArr C. atgt a) (\<lambda>X\<in>DOb C. Did C X)
      (\<lambda>u\<in>DArr C \<times> DArr C. Dcomp C (pfst u) (psnd u))"

subsection \<open>The category of small presheaves\<close>

text \<open>\<open>cgraph C Y x\<close>: the edges of the comma category \<open>(x \<down> G)\<close>, for \<open>Y = \<langle>K, G\<rangle>\<close>.\<close>

abbreviation cverts :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "cverts C Y x \<equiv> comma_verts C (ix Y) (dg Y) x"

abbreviation cgraph :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "cgraph C Y x \<equiv> comma_edges C (ix Y) (dg Y) x"

definition PArr :: "cls \<Rightarrow> cls"
  where "PArr C =
    \<lbrace>a. \<exists>\<^sub>s X Y \<phi>. a = \<langle>\<langle>X, Y\<rangle>, \<phi>\<rangle> \<and> X \<in> DOb C \<and> Y \<in> DOb C \<and>
      \<phi> = (\<lambda>j\<in>Ob (ix X). \<phi> \<cdot> j) \<and>
      (\<forall>\<^sub>s j. j \<in> Ob (ix X) \<longrightarrow>
        (\<exists>\<^sub>s v. v \<in> cverts C Y (dg X \<cdot>\<^sub>o j) \<and> \<phi> \<cdot> j = cc (cgraph C Y (dg X \<cdot>\<^sub>o j)) v)) \<and>
      (\<forall>\<^sub>s u k f. u \<in> Arr (ix X) \<longrightarrow> \<langle>k, f\<rangle> \<in> \<phi> \<cdot> tgt\<^bsub>ix X\<^esub> u \<longrightarrow>
        \<langle>k, f \<circ>\<^bsub>C\<^esub> dg X \<cdot>\<^sub>a u\<rangle> \<in> \<phi> \<cdot> src\<^bsub>ix X\<^esub> u)\<rbrace>"

definition Pid :: "cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Pid C X =
    \<langle>\<langle>X, X\<rangle>, \<lambda>j\<in>Ob (ix X). cc (cgraph C X (dg X \<cdot>\<^sub>o j)) \<langle>j, id\<^bsub>C\<^esub> (dg X \<cdot>\<^sub>o j)\<rangle>\<rangle>"

text \<open>
  \<open>Pcomp C b a\<close>: the composite \<open>b\<close> after \<open>a\<close>. At \<open>j\<close>, take any \<open>\<langle>k, f\<rangle>\<close> in the component \<open>a\<^sub>j\<close> and
  any \<open>\<langle>l, g\<rangle>\<close> in the component \<open>b\<^sub>k\<close>; the composite at \<open>j\<close> is the component of \<open>\<langle>l, g \<circ> f\<rangle>\<close>. It is
  written as the class of everything connected to some such \<open>\<langle>l, g \<circ> f\<rangle>\<close>, which involves no
  choice of representatives.
\<close>

definition Pcomp :: "cls \<Rightarrow> cls \<Rightarrow> cls \<Rightarrow> cls"
  where "Pcomp C b a =
    \<langle>\<langle>asrc a, atgt b\<rangle>,
      \<lambda>j\<in>Ob (ix (asrc a)).
        \<lbrace>w. \<exists>\<^sub>s k f l g. \<langle>k, f\<rangle> \<in> body a \<cdot> j \<and> \<langle>l, g\<rangle> \<in> body b \<cdot> k \<and>
          conn (cgraph C (atgt b) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>l, g \<circ>\<^bsub>C\<^esub> f\<rangle> w\<rbrace>\<rangle>"

definition PSh :: "cls \<Rightarrow> cls"
  where "PSh C =
    mkcat (DOb C) (PArr C) (\<lambda>a\<in>PArr C. asrc a) (\<lambda>a\<in>PArr C. atgt a) (\<lambda>X\<in>DOb C. Pid C X)
      (\<lambda>u\<in>PArr C \<times> PArr C. Pcomp C (pfst u) (psnd u))"

subsection \<open>From diagrams to presheaves\<close>

definition colim_functor :: "cls \<Rightarrow> cls"
  where "colim_functor C =
    mkfun (\<lambda>X\<in>DOb C. X)
      (\<lambda>a\<in>DArr C.
        \<langle>\<langle>asrc a, atgt a\<rangle>,
          \<lambda>j\<in>Ob (ix (asrc a)).
            cc (cgraph C (atgt a) (dg (asrc a) \<cdot>\<^sub>o j)) \<langle>afun a \<cdot>\<^sub>o j, anat a \<cdot> j\<rangle>\<rangle>)"

subsection \<open>Final reindexings\<close>

text \<open>
  \<open>W0 C\<close>: the arrows \<open>w : \<langle>J', F'\<rangle> \<rightarrow> \<langle>J, F\<rangle>\<close> of \<open>Diag C\<close> whose functor part \<open>q\<close> is final, with
  \<open>F' = F \<circ> q\<close> as functors on \<open>J'\<close> and with every component of the transformation an identity.
\<close>

definition W0 :: "cls \<Rightarrow> cls"
  where "W0 C =
    \<lbrace>w. w \<in> DArr C \<and>
      final_functor (afun w) (ix (asrc w)) (ix (atgt w)) \<and>
      agree (ix (asrc w)) (dg (asrc w)) (fcomp (ix (asrc w)) (dg (atgt w)) (afun w)) \<and>
      (\<forall>\<^sub>s j. j \<in> Ob (ix (asrc w)) \<longrightarrow> anat w \<cdot> j = id\<^bsub>C\<^esub> (dg (asrc w) \<cdot>\<^sub>o j))\<rbrace>"

subsection \<open>Class existence for this vocabulary\<close>

lemma dfun_ix [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. ix (T x))" unfolding ix_def by dfn
lemma dfun_dg [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. dg (T x))" unfolding dg_def by dfn
lemma dfun_asrc [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. asrc (T x))" unfolding asrc_def by dfn
lemma dfun_atgt [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. atgt (T x))" unfolding atgt_def by dfn
lemma dfun_body [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. body (T x))" unfolding body_def by dfn
lemma dfun_afun [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. afun (T x))" unfolding afun_def by dfn
lemma dfun_anat [dfn_rules]: "dcls T \<Longrightarrow> dfun (\<lambda>x. anat (T x))" unfolding anat_def by dfn

lemma dcls_DOb [dfn_rules]: "dcls C \<Longrightarrow> dcls (\<lambda>x. DOb (C x))"
  unfolding DOb_def by dfn

lemma dcls_DArr [dfn_rules]: "dcls C \<Longrightarrow> dcls (\<lambda>x. DArr (C x))"
  unfolding DArr_def by dfn

lemma dfun_Did [dfn_rules]: "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dfun (\<lambda>x. Did (C x) (X x))"
  unfolding Did_def by dfn

lemma dfun_Dcomp [dfn_rules]: "dcls C \<Longrightarrow> dcls B \<Longrightarrow> dcls A \<Longrightarrow> dfun (\<lambda>x. Dcomp (C x) (B x) (A x))"
  unfolding Dcomp_def by dfn

lemma dcls_Diag [dfn_rules]: "dcls C \<Longrightarrow> dcls (\<lambda>x. Diag (C x))"
  unfolding Diag_def by dfn

lemma dcls_PArr [dfn_rules]: "dcls C \<Longrightarrow> dcls (\<lambda>x. PArr (C x))"
  unfolding PArr_def by dfn

lemma dfun_Pid [dfn_rules]: "dcls C \<Longrightarrow> dcls X \<Longrightarrow> dfun (\<lambda>x. Pid (C x) (X x))"
  unfolding Pid_def by dfn

lemma dfun_Pcomp [dfn_rules]: "dcls C \<Longrightarrow> dcls B \<Longrightarrow> dcls A \<Longrightarrow> dfun (\<lambda>x. Pcomp (C x) (B x) (A x))"
  unfolding Pcomp_def by dfn

lemma dcls_PSh [dfn_rules]: "dcls C \<Longrightarrow> dcls (\<lambda>x. PSh (C x))"
  unfolding PSh_def by dfn

lemma dcls_colim_functor [dfn_rules]: "dcls C \<Longrightarrow> dcls (\<lambda>x. colim_functor (C x))"
  unfolding colim_functor_def by dfn

lemma dcls_W0 [dfn_rules]: "dcls C \<Longrightarrow> dcls (\<lambda>x. W0 (C x))"
  unfolding W0_def by dfn

end
