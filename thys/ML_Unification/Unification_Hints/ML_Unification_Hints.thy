\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Hints\<close>
theory ML_Unification_Hints
  imports
    ML_Generic_Data_Utils
    ML_Term_Index
    ML_Unifiers
    ML_Unification_Parsers
begin

paragraph \<open>Summary\<close>
text \<open>A generalisation of unification hints, originally introduced in \<^cite>\<open>"unif-hints"\<close>.
We support a generalisation that
\<^enum> allows additional universal variables in premises
\<^enum> allows non-atomic left-hand sides for premises
\<^enum> allows arbitrary functions to perform the matching/unification of a hint with a disagreement pair.

General shape of a hint:
\<open>\<And>y1...yn. (\<And>x1...xn1. lhs1 \<equiv> rhs1) \<Longrightarrow> ... \<Longrightarrow> (\<And>x1...xnk. lhsk \<equiv> rhsk) \<Longrightarrow> lhs \<equiv> rhs\<close>
\<close>

ML_file\<open>unification_hints_base.ML\<close>
ML_file\<open>unification_hints.ML\<close>
ML_file\<open>term_index_unification_hints.ML\<close>

text \<open>We now set up two unifiers using unification hints. The first one allows for recursive
applications of unification hints when unifying a hint's conclusion lhs \<equiv> rhs" with a goal
"lhs' \<equiv> rhs'".
The second only uses a combination of higher-order pattern and first-order unification.
This particularly implies that recursive applications of unification hints have to be made explicit
in the hint itself (cf. @{dir "../Examples"}).

While the former can be convenient for local hint registrations and quick developments,
it is advisable to use the second for global hints to avoid unexpected looping behaviour.\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unification_Hints_Rec
    and functor_name = Term_Index_Unification_Hints
    and id = \<open>"rec"\<close>
    and more_args = \<open>
      structure TI = Discrimination_Tree
      val init_args = {
        concl_unifier = SOME Standard_Mixed_Unification.first_higherp_first_comb_higher_unify,
        prems_unifier = SOME (Standard_Mixed_Unification.first_higherp_first_comb_higher_unify
          |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
        normalisers = SOME Standard_Mixed_Unification.norms_first_higherp_first_comb_higher_unify,
        retrieval = SOME (Term_Index_Unification_Hints_Args.mk_sym_retrieval
          TI.norm_term TI.unifiables),
        hint_preprocessor = SOME (K I)
      }\<close>}
\<close>
local_setup \<open>Standard_Unification_Hints_Rec.setup_attribute NONE\<close>

text\<open>Standard unification hints using
@{ML Standard_Mixed_Unification.first_higherp_first_comb_higher_unify}
when looking for hints are accessible via @{attribute rec_uhint}.

\<^emph>\<open>Note:\<close> when we retrieve a potential unification hint with conclusion "lhs \<equiv> rhs" for a goal
"lhs' \<equiv> rhs'", we only consider those hints whose lhs potentially higher-order unifies with
lhs' or rhs' \<^emph>\<open>without using hints\<close>. For otherwise, any hint "lhs \<equiv> rhs" applied to a goal
"rhs \<equiv> lhs" leads to an immediate loop.\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unification_Hints
    and functor_name = Term_Index_Unification_Hints
    and id = \<open>""\<close>
    and more_args = \<open>
      structure TI = Discrimination_Tree
      val init_args = {
        concl_unifier = SOME Higher_Ordern_Pattern_First_Decomp_Unification.unify,
        prems_unifier = SOME (Standard_Mixed_Unification.first_higherp_first_comb_higher_unify
          |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
        normalisers = SOME Standard_Mixed_Unification.norms_first_higherp_first_comb_higher_unify,
        retrieval = SOME (Term_Index_Unification_Hints_Args.mk_sym_retrieval
          TI.norm_term TI.unifiables),
        hint_preprocessor = SOME (K I)
      }\<close>}
\<close>
local_setup \<open>Standard_Unification_Hints.setup_attribute NONE\<close>

text\<open>Standard unification hints using @{ML Higher_Ordern_Pattern_First_Decomp_Unification.unify}
when looking for hints are accessible via @{attribute uhint}.

\<^emph>\<open>Note:\<close> there will be no recursive usage of unification hints when searching for potential
unification hints in this case. See also @{dir "../Examples"}.\<close>

declare [[ucombine add = \<open>Standard_Unification_Combine.eunif_data
  (Standard_Unification_Hints_Rec.try_hints
  |> Unification_Combinator.norm_unifier
    (#norm_term Standard_Mixed_Unification.norms_first_higherp_first_comb_higher_unify)
  |> K)
  (Standard_Unification_Combine.default_metadata Standard_Unification_Hints_Rec.binding)\<close>]]
and [[ucombine add = \<open>Standard_Unification_Combine.eunif_data
  (Standard_Unification_Hints.try_hints
  |> Unification_Combinator.norm_unifier
    (#norm_term Standard_Mixed_Unification.norms_first_higherp_first_comb_higher_unify)
  |> K)
  (Standard_Unification_Combine.default_metadata Standard_Unification_Hints.binding)\<close>]]


text\<open>Examples see @{dir "../Examples"}.\<close>

end
