theory Dissonance
imports Main

begin

lemma "\<Sum> {0..n::nat} = n*(n+1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n assume "\<Sum> {0..n::nat} = n*(n+1) div 2"
  thus "\<Sum> {0..Suc n} = Suc n*(Suc n+1) div 2" by simp
qed

text \<open>By pattern matching\<close>


lemma "\<Sum> {0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P(n)"
  thus "?P(Suc n)" by simp
qed

text \<open>By pattern cases\<close>


lemma "\<Sum> {0..n::nat} = n*(n+1) div 2"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed


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

lemma "sum_n_square n = (n * (n+1) * (2 * n + 1)) div 6"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  from this have "sum_n_square (Suc n) = Suc n * Suc n + n * (n + 1)* (2 * n + 1) div 6" by simp
  have "\<dots> = (Suc n * Suc n) * 6 div 6 + n * (Suc n)* (2 * n + 1) div 6" by simp
  have "\<dots> = ((Suc n * Suc n) * 6 + n * (Suc n) * (2 * n + 1)) div 6" by simp
  have "\<dots> = ((Suc n) * (n + 1) * 6 + (Suc n) * n * (2 * n + 1)) div 6" by simp
  (* dafuck simplify can't distributive *)
  have "\<dots> = ((Suc n) * ((n + 1) * 6 + n * (2 * n + 1))) div 6" by auto
  have "\<dots> = ((Suc n) * ((2 * n + 3) * 2 + 2 * n + n * (2 * n + 1))) div 6" by simp
  have "\<dots> = ((Suc n) * ((2 * n + 3) * 2 + n * (2 * n + 3))) div 6" using add_mult_distrib2 by auto
  have "\<dots> = ((Suc n) * (2 * n + 3) * (n + 2)) div 6" by (simp add: add.commute add_mult_distrib2 mult.commute)  
  then have "\<dots> = (Suc n * (Suc n + 1) * (2 * Suc n + 1)) div 6" by (smt One_nat_def Suc_1 add.commute add.right_neutral add_Suc mult_Suc_right numeral_3_eq_3 semiring_normalization_rules(16))
  thus ?case .
end