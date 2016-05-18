theory LundfallErfurtEx04
imports Main
begin





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
  Also, the way the implication is interpreted in classical logic is not the way we necessarily
  use it in everyday language. The assumption 'it is not that case that (if I pray, my prayers will
  be answered)' is different from 'if I pray, my prayers will not be answered', which is probably
  a more reasonable assumption in the context of gods nonexistence.\<close>  


text \<open>Ex 2\<close>

fun sum_n :: "nat \<Rightarrow> nat" where
  "sum_n 0 = 0" |
  "sum_n (Suc n) = Suc n + sum_n n"

lemma "sum_n n = n * (n + 1) div 2"

proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  from this have "sum_n (Suc n) = (Suc n) * ((Suc n) + 1) div 2" by simp
  thus ?case .
qed

fun sum_n_square :: "nat \<Rightarrow> nat" where
  "sum_n_square 0 = 0" |
  "sum_n_square (Suc n) = Suc n * Suc n + sum_n_square n"

lemma "sum_n_square n = (n * (n + 1) * (2 * n + 1)) div 6"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  from this have "sum_n_square (Suc n) = Suc n * Suc n + sum_n_square n" by simp
  then have "sum_n_square (Suc n) = Suc n * Suc n + (n * (n + 1) * (2 * n + 1)) div 6" by (simp add: Suc.IH)
  then have "sum_n_square (Suc n) = ((Suc n) * (n + 1) * 6 + (Suc n) * n * (2 * n + 1)) div 6" by simp
  then have "sum_n_square (Suc n) = ((Suc n) * ((n + 1) * 6) + (Suc n) * n * (2 * n + 1)) div 6" using mult.assoc [of "Suc n" "n + 1" 6] by simp
  then have "sum_n_square (Suc n) = ((Suc n) * ((n + 1) * 6) + (Suc n) * (n * (2 * n + 1))) div 6" using mult.assoc [of "Suc n" "n" "2 * n + 1"] by simp
  then have "sum_n_square (Suc n) = ((Suc n) * (((n + 1) * 6) + (n * (2 * n + 1)))) div 6" using add_mult_distrib2 [of "Suc n" "(n + 1) * 6"  "n * (2 * n + 1)"] by simp
  then have "sum_n_square (Suc n) = ((Suc n) * ((2 * n + 3) * 2 + 2 * n + n * (2 * n + 1))) div 6" by simp
  then have "sum_n_square (Suc n) = ((Suc n) * ((2 * n + 3) * 2 + n * (2 * n + 3))) div 6" using add_mult_distrib2 by simp
  then have "sum_n_square (Suc n) = ((Suc n) * (2 * n + 3) * (n + 2)) div 6" by (simp add: add_mult_distrib2 mult.commute)
  then have "sum_n_square (Suc n) = (Suc n * (2 * n + 3) * (Suc n + 1)) div 6" by (simp add: add_mult_distrib2 mult.commute)
  then have "sum_n_square (Suc n) = (Suc n * ((2 * n + 3) * (Suc n + 1))) div 6" by (simp add: add_mult_distrib2 mult.commute)
  then have "sum_n_square (Suc n) = (Suc n * ((Suc n + 1) * (2 * n + 3))) div 6" by (simp add: mult.commute)
  then have "sum_n_square (Suc n) = (Suc n * ((Suc n + 1) * (2 * n + (2 * 1 + 1)))) div 6" by (simp add: mult.assoc [symmetric])
  then have "sum_n_square (Suc n) = (Suc n * ((Suc n + 1) * (2 * Suc n + 1))) div 6" by (simp add: add_mult_distrib2)
  then have "sum_n_square (Suc n) = (Suc n * (Suc n + 1) * (2 * Suc n + 1)) div 6" using mult.assoc [of "Suc n" "Suc n + 1" "2 * Suc n + 1"] by simp
thus ?case .
qed

lemma flipping:
  assumes "A \<longrightarrow> B"
  shows "\<not> B \<longrightarrow> \<not> A"
proof -
  {
    assume 1: "\<not>B"
    {
      assume 2: "A"
      from assms 2 have 3: "B" by (rule mp)
      from 1 3 have "False" by (rule notE)
    }
    from this have "\<not>A" by (rule notI)
  }
  from this have "\<not> B \<longrightarrow> \<not> A" by (rule impI)
thus ?thesis .
qed

theorem Ex3:
assumes 1: "\<forall>X. \<not>rich(X) \<longrightarrow> rich (parent(X))"
shows "\<exists>X. rich(parent(parent(X)))\<and>rich(X)"
proof cases 
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
  assume 8: "\<not>(\<forall>X. \<not>rich(X))"
  from 8 have "\<exists>X. rich(X)" by simp
  then obtain y where 9: "rich(y)" by (rule exE)
  { 
    assume 11: "\<not>rich(parent(parent(y)))"
    {
      fix x
      from assms have "\<not>rich(x) \<longrightarrow> rich(parent(x))" by (rule allE)
      then have "\<not>rich(parent(x)) \<longrightarrow> \<not>(\<not>rich(x))" by (rule flipping)
      then have "\<not>rich(parent(x)) \<longrightarrow> rich(x)" by simp
    }
    from this have 12: "\<forall>x. \<not>rich(parent(x)) \<longrightarrow> rich(x)" by (rule allI)
    from 11 12 have 13: "rich(parent(y))" by simp
    from 1 11 have 14: "rich(parent(parent(parent(y))))" by simp
    from 13 14 have "rich(parent(parent(parent(y)))) \<and> rich(parent(y))" by simp
    then have "\<exists>y. rich(parent(parent(y)))\<and>rich(y)" by (rule exI)
    } note case1 = this
    { 
      assume 15: "rich(parent(parent(y)))"
      from 9 15 have "rich(parent(parent(y))) \<and> rich(y)" by simp
      then have "\<exists>y. rich(parent(parent(y)))\<and>rich(y)" by (rule exI)
    } note case2 = this
    from case1 case2 show "\<exists>y. rich(parent(parent(y))) \<and> rich(y)" by cases   
qed
end