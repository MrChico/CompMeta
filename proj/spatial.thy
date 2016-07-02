theory spatial
imports Main
begin

(*The mutually recursive datatypes of processes and names*)
datatype P = Null             ("\<^bold>0")
           | input n n P      ("_\<leftarrow>_._" 60)
           | lift n P         ("_\<triangleleft>_\<triangleright>" 20)
           | drop n           ("\<acute>_`" 30)
           | par P P          (infixl "\<parallel>" 51)    
     and n = quote P          ("`_\<acute>")

abbreviation zero :: n
  where "zero \<equiv> `\<^bold>0\<acute>"

value "zero \<leftarrow> zero.\<^bold>0"
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"

(*Structural congruence*)
axiomatization where
  Id: "\<^bold>0 \<parallel> p = p" and
  Sym: "P \<parallel> Q = Q \<parallel> P" and
  Assoc: "(P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R)" 

theorem test:
  assumes "Id" and "Sym"
  shows "p \<parallel> \<^bold>0 = p"
  

(*Name equivalence*)

end