theory Instantiate_Term_Antiquotation
  imports Pure
begin

ML_file \<open>instantiate_term_antiquotation.ML\<close>

setup \<open>ML_Context.add_antiquotation \<^binding>\<open>Term\<close> true Instantiate_Term_Antiquotation.antiquotation_Term\<close>

end
