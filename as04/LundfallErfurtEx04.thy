theory LundfallErfurtEx04
imports Main
begin

lemma flipping:
  assumes "A \<longrightarrow> B"
  shows "\<not> B \<longrightarrow> \<not> A"
using assms by blast


lemma fromEx2:
  assumes 1: "\<not>A"
  shows "A \<longrightarrow> B"
  proof - 
    {
      assume 2: "A"
      {
        assume 3: "\<not>B"
        from 1 2 have "False" by (rule notE)
      }
      from this have "B" by (rule ccontr)
    }
    from this have "A \<longrightarrow> B" by (rule impI)
  thus ?thesis .
qed

theorem ontological:
assumes 1: "\<not>G \<longrightarrow> \<not>(P \<longrightarrow> A)" and
2: "\<not>P"
shows "G"
proof -
  {
    assume 3: "\<not>G"
    from 1 3 have 4: "\<not>(P \<longrightarrow> A)" by (rule mp)
    from 2 have 5: "P \<longrightarrow> A" by (rule fromEx2)
    from 4 5 have "False" by (rule notE)
  }
  from this have "G" by (rule ccontr)
thus ?thesis .
qed

text \<open>One argument could be that we do not accept the law of double negation. Then we cannot 
  conclude the existence of god from refuting the non-existence of god.
  Also, the way the implication is interpreted in classical logic is not they way we necessarily
  use it in everyday language. The assumption 'it is not that case that (if I pray, my prayers will
  be answered)' is different from 'if I pray, my prayers will not be answered', which is probably
  a more reasonable assumption in the context of gods nonexistence.\<close>  
theorem test:
  assumes "\<not>A \<longrightarrow> B" 
  shows "A \<or> B" 
using assms by auto


theorem Ex3:
assumes 1: "\<forall>X. \<not>rich(X) \<longrightarrow> rich (parent(X))"
shows "\<exists>X. rich(parent(parent(X)))\<and>rich(X)"
proof cases 
  { 
    assume 2: "\<forall>X. \<not>rich(X)"
    {
      assume "\<not>(\<exists>X. rich(parent(parent(X))) \<and> rich(X))"
      fix X
      from 2 have 3: "\<not>rich(X)" by (rule allE)
      from 1 have 4: "\<not>rich(X) \<longrightarrow> rich(parent(X))" by (rule allE)
      from 4 3 have 5: "rich(parent(X))" by (rule mp)
      then have 6: "\<exists>X. rich(X)" by (rule exI)
      from 2 have 7: "\<not> (\<exists> X. rich(X))" by simp
      from 7 6 have "False" by (rule notE)
   }
  from this show "\<exists>X. rich(parent(parent(X)))\<and>rich(X)" by (rule ccontr)
next
  {
    assume 8: "\<not>(\<forall>X. \<not>rich(X))"
    from 8 have "\<exists>X. rich(X)" by simp
    then obtain y where 9: "rich(y)" by (rule exE)
 {
       fix x
       from assms have "\<not>rich(x) \<longrightarrow> rich (parent(x))" by (rule allE)
       then have "rich(x) \<or> rich(parent(x))" by (rule test)
    }

      
qed
end