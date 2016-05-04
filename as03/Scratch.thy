theory Scratch
imports Main 

begin

subsection \<open>Exercise 1\<close>

theorem 
  assumes a: "(\<forall> x. P x) \<and> (\<forall> x. Q x)"
  shows "\<forall> x. P x \<and> Q x"
proof -
  {
    fix x
    from a have "\<forall> x. P x" by (rule conjunct1)
    then  have px: "P x" by (rule allE)
    from a have "\<forall> x. Q x" by (rule conjunct2)
    then have "Q x" by (rule allE)
    with px have "P x \<and> Q x" by (rule conjI)    
  }
  thus ?thesis by (rule allI)
qed

lemma
  assumes "\<exists> x. P x \<and> Q x"
  shows "\<exists> x. P x"
proof -
  from assms obtain x where 1: "P x \<and> Q x" by (rule exE)
  then have xx: "P x" by (rule conjunct1)
  then show ?thesis by (rule exI)
qed


lemma
  assumes "\<forall> x. P x"
  shows "\<exists>x. P x"
proof -
  fix x
  from assms have "P x" by (rule allE)
  then have "\<exists> x. P x" by (rule exI)
  thus ?thesis .
qed

lemma
  shows "((\<forall> x. P x) \<and> (\<forall> x. Q x)) \<longleftrightarrow> (\<forall> x. P x \<and> Q x)"
proof -
  {
    assume a: "(\<forall> x. P x) \<and> (\<forall> x. Q x)"
    {
      fix x
      from a have "\<forall> x. P x" by (rule conjunct1)
      then have b: "P x" by (rule allE)
      from a have "\<forall> x. Q x" by (rule conjunct2)
      then have c: "Q x" by (rule allE)
      from b c have "P x \<and> Q x" by (rule conjI)
    }
    then have "(\<forall> x. P x \<and> Q x)" by (rule allI)
  } note lhs = this
  {
    assume a: "(\<forall> x. P x \<and> Q x)"
    {
      fix x
      from a have "P x \<and> Q x" by (rule allE)
      then have "P x" by (rule conjunct1)
    }
    then have b: "\<forall> x. P x" by (rule allI)
    {
      fix x
      from a have "P x \<and> Q x" by (rule allE)
      then have "Q x" by (rule conjunct2)
    }
    then have c: "\<forall> x. Q x" by (rule allI)
    from b c have "(\<forall> x. P x) \<and> (\<forall> x. Q x)" by (rule conjI) 
  } note rhs = this
  from lhs rhs show ?thesis by (rule iffI)
qed

subsection \<open>Exercise 2\<close>

theorem 
  shows "(\<exists> x. \<forall> y. P x y) \<longrightarrow> (\<forall> y. \<exists> x. P x y)"
  nitpick
proof -
  {
    assume a: "\<exists> x. \<forall> y. P x y"
    {
      fix y
      from a obtain x where 1: "\<forall> y. P x y" by (rule exE)
      from this have "P x y" by (rule allE)
      from this have "\<exists> x. P x y" by (rule exI)
    }
    from this have "\<forall> y. \<exists> x. P x y" by (rule allI)
  }  
  from this show ?thesis by (rule impI)
qed

theorem 
  shows "((\<forall> x. P x) \<longrightarrow> Q) \<longleftrightarrow> ((\<exists> x. P x) \<longrightarrow> Q)"
  nitpick
  (*
    'a = {a, b, c, d}
    Q = False
    P(a) = False
    P(b) = False
    P(c) = False
    P(d) = True
  *)
oops

lemma
  shows "((\<forall> x. P x) \<or> (\<forall> x. Q x)) \<longleftrightarrow> (\<forall> x. (P x \<or> Q x))"
proof -
nitpick
  (*
    'a = {a, b}
    P(a) = False
    P(b) = True
    Q(a) = True
    Q(b) = False
  *)
oops

lemma
  shows "((\<exists> x. P x) \<or> (\<exists> x. Q x)) \<longleftrightarrow> (\<exists> x. (P x \<or> P x))"
  nitpick
  (*
    'a = {a,b,c}
    P(a) = False
    P(b) = False
    P(c) = False
    Q(a) = False
    Q(b) = False
    Q(c) = True
  *)
oops

lemma
  shows "(\<forall> x. \<exists> y. P x y) \<longrightarrow> (\<exists> y. \<forall> x. P x y)"
  nitpick
  (*
    'a = {a,b}
    P(a,a) = False
    P(a,b) = True
    P(b,a) = True
    P(b,b) = False
  *)
oops

lemma
  shows "(\<not>(\<forall> x. P x)) \<longleftrightarrow> (\<exists> x. \<not> P x)"
proof -
  {
    assume "\<not>(\<forall> x. P x)"
  } note lhs = this
  {
  } note rhs = this
  sorry