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

text \<open>Exercise 3\<close>

typedecl bird

consts call :: "bird \<Rightarrow> bird \<Rightarrow> bird" (infix "\<cdot>" 51)
definition "mockingbird" where "mockingbird M \<equiv> \<forall> x. M \<cdot> x = x \<cdot> x"
definition "composesWith" where "composesWith C A B \<equiv> \<forall> x. A \<cdot> (B \<cdot> x) = C \<cdot> x"
definition "isfond" where "isfond A B \<equiv> A \<cdot> B = B"

axiomatization where
  C1: "\<exists> C. composesWith C A B" and
  C2: "\<exists> M. mockingbird M"

lemma
assumes a1: "mockingbird M"
assumes a2: "A \<cdot> (M \<cdot> x) = B"
shows "A \<cdot> (x \<cdot> x ) = B"
proof -
  from a1 have "\<forall> x . M \<cdot> x = x \<cdot> x" unfolding mockingbird_def .
  then have mock: "M \<cdot> x = x \<cdot> x" by (rule allE)
  from mock a2 show ?thesis by (rule subst)
qed

theorem "first-rumor": "\<forall> x. \<exists> y. isfond x y"
proof - 
  {
    fix x
    from C2 obtain M where 1: "mockingbird M" by (rule exE)
    from 1 have 2: "\<forall> x . M \<cdot> x = x \<cdot> x" unfolding mockingbird_def .
    from 2 have 3: "M \<cdot> (M \<cdot> M) = (M \<cdot> M) \<cdot> (M \<cdot> M)" by (rule allE)
    from C1 obtain C where 4: "composesWith C M M" by (rule exE)
    then have 5: "\<forall> x. M \<cdot> (M \<cdot> x) = C \<cdot> x" unfolding composesWith_def .
    then have "M \<cdot> (M \<cdot> C) = C \<cdot> C" by (rule allE)
    from 5 have 6: "M \<cdot> (M \<cdot> M) = C \<cdot> M" by (rule allE)
    from 3 6 have 7: "(M \<cdot> M) \<cdot> (M \<cdot> M) = C \<cdot> M" by simp
    have "M \<cdot> M = (x \<cdot> M) \<cdot> M" sorry
    then have "M = x \<cdot> M" sorry
    have 8: "x \<cdot> (C \<cdot> M) = C \<cdot> M" sorry
    from 7 6 8 have 9: "x \<cdot> (M \<cdot> (M \<cdot> M)) = (M \<cdot> M) \<cdot> (M \<cdot> M)" by simp
    from 3 9 have "x \<cdot> (M \<cdot> (M \<cdot> M)) = M \<cdot> (M \<cdot> M)" by simp
    then have "isfond x (M \<cdot> (M \<cdot> M))" unfolding isfond_def .
    then have "\<exists> y. isfond x y" by (rule exI)
  }
  from this have "\<forall> x. \<exists> y. isfond x y" by (rule allI)
  thus ?thesis .
qed

theorem "second-rumor": "\<exists> x. \<forall> y. \<not>(isfond x y)"   
nitpick [user_axioms]
oops 
end