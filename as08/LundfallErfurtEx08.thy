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

theorem itoii:
  assumes "transitive"
  shows "\<forall>\<phi>.\<lfloor>\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>"
proof -
  show ?thesis using assms by blast
qed


theorem iitoiii:
  assumes "\<forall>\<phi>.\<lfloor>\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>"
  shows "\<lfloor>\<^bold>\<box>\<^bold>\<top>\<^bold>\<rightarrow>\<^bold>\<box>\<^bold>\<box>\<^bold>\<top>\<rfloor>"
proof -
show ?thesis using assms by blast
qed

theorem iitoi:
  assumes "\<forall>\<phi>.\<lfloor>\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>"
  shows "transitive"
proof -
show ?thesis using assms by blast
qed

theorem iiitoi:
  assumes "\<lfloor>\<^bold>\<box>\<^bold>\<top>\<^bold>\<rightarrow>\<^bold>\<box>\<^bold>\<box>\<^bold>\<top>\<rfloor>"
  shows "\<forall>\<phi>.\<lfloor>\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>"
sorry


theorem omfg:
  assumes "\<lfloor>p\<rfloor>" (* \<forall>w. p(w) *)
  shows "\<lfloor>\<^bold>\<box>p\<rfloor>"  (* \<forall>w. \<forall> v. ( w r v \<^bold>\<rightarrow> p(v) ) *)
proof -
show ?thesis by (simp add: assms)
qed

theorem omfg2:
  shows "\<lfloor>p\<^bold>\<rightarrow>\<^bold>\<box>p\<rfloor>"
  nitpick
(*
  Free variable:
    p = (\<lambda>x. _)(i\<^sub>1 := False, i\<^sub>2 := True)
  Skolem constants:
    v = i\<^sub>1
    w = i\<^sub>2
*)
oops



end
