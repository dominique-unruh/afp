section \<open>Axioms of references\<close>

theory Axioms
  imports Main
begin

class domain
instance prod :: (domain,domain) domain
  by intro_classes

typedecl 'a update
axiomatization comp_update :: "'a::domain update \<Rightarrow> 'a update \<Rightarrow> 'a update" where
  comp_update_assoc: "comp_update (comp_update a b) c = comp_update a (comp_update b c)"
axiomatization id_update :: "'a::domain update" where
  id_update_left: "comp_update id_update a = a" and
  id_update_right: "comp_update a id_update = a"

axiomatization prereference :: \<open>('a::domain update \<Rightarrow> 'b::domain update) \<Rightarrow> bool\<close>
axiomatization where
  comp_prereference: "prereference F \<Longrightarrow> prereference G \<Longrightarrow> prereference (G \<circ> F)" and
  id_prereference: \<open>prereference id\<close>
for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close> and G :: \<open>'b update \<Rightarrow> 'c::domain update\<close>

axiomatization where
  prereference_mult_right: \<open>prereference (\<lambda>a. comp_update a z)\<close> and
  prereference_mult_left: \<open>prereference (\<lambda>a. comp_update z a)\<close>
    for z :: "'a::domain update"

axiomatization tensor_update :: \<open>'a::domain update \<Rightarrow> 'b::domain update \<Rightarrow> ('a\<times>'b) update\<close> 
  where tensor_extensionality: "prereference F \<Longrightarrow> prereference G \<Longrightarrow> (\<And>a b. F (tensor_update a b) = G (tensor_update a b)) \<Longrightarrow> F = G"
  for F G :: \<open>('a\<times>'b) update \<Rightarrow> 'c::domain update\<close>

axiomatization where tensor_update_mult: \<open>comp_update (tensor_update a c) (tensor_update b d) = tensor_update (comp_update a b) (comp_update c d)\<close>
  for a b :: \<open>'a::domain update\<close> and c d :: \<open>'b::domain update\<close>

axiomatization reference :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> bool\<close>
axiomatization where
  reference_prereference: "reference F \<Longrightarrow> prereference F" and
  reference_comp: "reference F \<Longrightarrow> reference G \<Longrightarrow> reference (G \<circ> F)"  and
  reference_mult: "reference F \<Longrightarrow> comp_update (F a) (F b) = F (comp_update a b)" and
  reference_of_id: \<open>reference F \<Longrightarrow> F id_update = id_update\<close> and
  reference_id: \<open>reference (id :: 'a update \<Rightarrow> 'a update)\<close>
for F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'b update \<Rightarrow> 'c::domain update" 

axiomatization where reference_tensor_left: \<open>reference (\<lambda>a. tensor_update a id_update)\<close>
axiomatization where reference_tensor_right: \<open>reference (\<lambda>a. tensor_update id_update a)\<close>

axiomatization reference_pair ::
  \<open>('a::domain update \<Rightarrow> 'c::domain update) \<Rightarrow> ('b::domain update \<Rightarrow> 'c update)
         \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  reference_pair_is_reference: \<open>reference F \<Longrightarrow> reference G \<Longrightarrow> (\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a))
       \<Longrightarrow> reference (reference_pair F G)\<close> and
  reference_pair_apply: \<open>reference F \<Longrightarrow> reference G \<Longrightarrow> (\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a))
       \<Longrightarrow> (reference_pair F G) (tensor_update a b) = comp_update (F a) (G b)\<close>

end
