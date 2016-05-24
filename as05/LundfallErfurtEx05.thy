theory LundfallErfurtEx05
imports Main
begin
text \<open>Exercise 1\<close>
theorem ex1 :
fixes "f" :: "bool \<Rightarrow> bool"
shows "f (f (f n)) = f n"
sledgehammer
by smt
(*  show "f (f (f n)) = f n" sorry
qed
*)
text \<open>Exercise 2\<close>
abbreviation leibnizEq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "=L"  42 ) where
"a =L b \<equiv> \<forall>P. P a \<longrightarrow> P b"

lemma refl:
assumes "a =L b"
shows "\<forall>P. P a \<longleftrightarrow> P b"
proof - 
  {
    fix P
    {
      assume 1: "P b"
      {
        assume 2: "\<not> (P a)"
        from assms have 3: "\<not> (P a) \<longrightarrow> \<not> (P b)" by (rule allE)
        from 3 2 have 4: "\<not> P b" by (rule mp)
        from 4 1 have "False" by (rule notE)
      }
      from this have "P a" by (rule ccontr)
    } note RtoL = this
    {
      assume 5: "P a"
      from assms have 6: "P a \<longrightarrow> P b" by (rule allE)
      from 6 5 have "P b" by (rule mp)
    } note LtoR = this
    from LtoR RtoL have "P a \<longleftrightarrow> P b" by (rule iffI)
  }
  from this have "\<forall> P . P a \<longleftrightarrow> P b" by (rule allI)
thus ?thesis .
qed
  
lemma N2:
assumes "a =L b"
shows "a = b"
proof -
    from assms have 2: "a = a \<longrightarrow> a = b" by (rule allE)
    have 3: "a = a" by simp
    from 2 3 have 4: "a = b" by (rule mp)
thus ?thesis .
qed

lemma N3:
assumes "a = b"
shows "a =L b"
proof -
  {
    fix P
    {
      assume 1: "P a"
      from assms 1 have "P b" by simp
    }
    from this have "P a \<longrightarrow> P b" by (rule impI)
  } from this have "\<forall> P. P a \<longrightarrow> P b" by (rule allI)
thus ?thesis .
qed
end