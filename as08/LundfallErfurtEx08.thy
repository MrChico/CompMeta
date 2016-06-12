theory LundfallErfurtEx08
imports QML Main
begin
section\<open>Exercise 1\<close>
text\<open>Consider the model consisting of two worlds w and w' where the following formulae holds:
A(w), A(w'), \<not>B(w), B(w'), C(w), \<not>C(w). In this model, A is globally valid, but not B \<^bold>\<longrightarrow> C. 
Thus A valid does not imply B \<^bold>\<longrightarrow> C valid.
However, since A, B is not globally valid, then the implication
"A, B valid implies C valid" is vacuously true\<close>
consts w :: i
consts w' :: i
consts A :: \<sigma>
consts B :: \<sigma>
consts C :: \<sigma>
theorem ex1:
assumes "\<lfloor>A \<^bold>\<and> B\<rfloor> \<longrightarrow> \<lfloor>C\<rfloor>"
shows "\<lfloor>A\<rfloor> \<longrightarrow> \<lfloor>B \<^bold>\<rightarrow> C\<rfloor>"
nitpick
(*
Nitpick found a counterexample for card i = 2:

  Skolem constant:
    w = i\<^sub>1
*)
oops
section \<open>Exercise 2\<close>

end
