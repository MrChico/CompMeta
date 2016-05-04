theory LundfallErfurtEx03
imports Main
begin
section \<open>Exercise 1\<close>
theorem "a)":
  assumes 1:"(\<forall>X. p X) \<and> (\<forall>X. q X)"
  shows "\<forall>X. p X \<and> q X"
    proof -
        {
          fix x
          from 1 have 2: "\<forall>X. p X" by (rule conjE)
          from 1 have 3: "\<forall>X. q X" by (rule conjE)
          from 2 have 4: "p x" by (rule allE)
          from 3 have 5: "q x" by (rule allE)
          from 4 5 have 6: "p x \<and> q x" by (rule conjI)
        }
        from this have "\<forall>x. (p x \<and> q x)" by (rule allI)
        thus ?thesis .
qed

theorem "b)":
  assumes 1: "\<forall>X. p X"
  shows "\<exists>X. p X"
  proof - 
    {
      fix x
      from 1 have 2: "p x" by (rule allE)
    }
    from this have "\<exists>X. p X" by (rule exI)
    thus ?thesis .
qed

theorem "c)":
  assumes 1: "\<exists>X. p X \<and> q X"
  shows "\<exists>X. p X"
  proof -
    {
      
      from 1 have 2: "p t \<and> q t" by (rule exE)
end