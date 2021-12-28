theory Test
imports Main
begin

datatype P = Par P P
           | A
           | B
           | C
           | D


value "T(T(B) B)"

abbreviation Set1 where "Set1 \<equiv> {A, B, C, D}"
abbreviation Set2 where "Set2 \<equiv> {B, C, D, A}"

abbreviation eq where "eq \<equiv> \<lambda> a::P set. \<lambda> b::P set. \<exists> f:: P \<Rightarrow> P. bij f"

value "eq Set1 Set2"



end