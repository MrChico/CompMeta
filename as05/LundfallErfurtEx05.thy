theory LundfallErfurtEx05
imports Main
begin

text \<open>Denis Erfurt - k0025944\<close>

text \<open>Exercise 1\<close>
theorem ex1:
fixes "f" :: "bool \<Rightarrow> bool"
shows "f (f (f n)) = f n"
proof -
  have "\<not> n \<or> n" by (rule excluded_middle)
  then show ?thesis
  proof
    assume 1: "\<not> n"
    have "\<not> f n \<or> f n" by (rule excluded_middle)
    then show ?thesis
    proof
      assume 2: "\<not> f n"
      then have "\<not> f(f(n))" using 1 by simp
      then have 4: "\<not> f(f(f(n)))" using 2 by simp
      from 2 4 show ?thesis by simp
    next
      assume 5: "f n"
      have "\<not> f(f(n)) \<or> f(f(n))" by (rule excluded_middle)
      then show ?thesis
      proof
        assume "\<not> f(f(n))"
        then have "f(f(f(n)))" using 1 5 by simp
        thus ?thesis using 5 by simp
      next 
        assume "f(f(n))"
        then have "f(f(f(n)))" using 5 by simp
        thus ?thesis using 5 by simp
      qed
    qed
  next
    assume 6: "n"
    have "\<not> f n \<or> f n" by (rule excluded_middle)
    then show ?thesis
    proof
      assume 7: "\<not> f n"
      have "\<not> f(f(n))\<or> f(f(n))" by (rule excluded_middle)
      thus ?thesis
      proof
        assume "\<not> f(f(n))"
        then have "\<not> f(f(f(n)))" using 7 by simp
        thus ?thesis using 7 by simp
      next
        assume "f(f(n))"
        then have "\<not> f(f(f(n)))" using 6 7 by simp
        thus ?thesis using 7 by simp
      qed
    next
      assume 8: "f n"
      then have "f(f(n))" using 6 by simp
      then have "f(f(f(n)))" using 6 8 by simp
      thus ?thesis using 8 by simp
    qed
  qed
qed

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

theorem "first-rumor": "\<forall> x. \<exists> y. isfond x y"
proof - 
  {
    fix x
    from C2 obtain M where 1: "mockingbird M" by (rule exE)
    from 1 have 2: "\<forall> z . M \<cdot> z = z \<cdot> z" unfolding mockingbird_def .
    from C1 obtain C where 4: "composesWith C x M" by (rule exE)
    then have 5: "\<forall> y. x \<cdot> (M \<cdot> y) = C \<cdot> y" unfolding composesWith_def .
    have "C \<cdot> C = C \<cdot> C" by simp
    from 2 have "M \<cdot> C = C \<cdot> C" by (rule allE)
    from 5 have 6: "x \<cdot> (M \<cdot> C) = C \<cdot> C" by (rule allE)
    from 2 5 have "x \<cdot> (M \<cdot> C) = M \<cdot> C" by simp
    then have "isfond x (M \<cdot> C)" unfolding isfond_def .
    then have "\<exists> y. isfond x y" by (rule exI)
  }
  from this have "\<forall> x. \<exists> y. isfond x y" by (rule allI)
  thus ?thesis .
qed
 
end