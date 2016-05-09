theory Scratch
imports Main 

begin

subsection \<open>Exercise 1\<close>

theorem "a)":
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

lemma "b)":
  assumes "\<exists> x. P x \<and> Q x"
  shows "\<exists> x. P x"
proof -
  from assms obtain x where 1: "P x \<and> Q x" by (rule exE)
  then have xx: "P x" by (rule conjunct1)
  then show ?thesis by (rule exI)
qed


lemma "c)":
  assumes "\<forall> x. P x"
  shows "\<exists>x. P x"
proof -
  fix x
  from assms have "P x" by (rule allE)
  then have "\<exists> x. P x" by (rule exI)
  thus ?thesis .
qed

lemma "d)":
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

theorem "a":
  shows "(\<exists> x. \<forall> y. P x y) \<longrightarrow> (\<forall> y. \<exists> x. P x y)"
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

theorem "b":
  shows "((\<forall> x. P x) \<longrightarrow> Q) \<longleftrightarrow> ((\<exists> x. P x) \<longrightarrow> Q)"
  proof 
  (*
    'a = {a, b, c, d}
    Q = False
    P(a) = False
    P(b) = False
    P(c) = False
    P(d) = True
  *)
oops

lemma "c":
  shows "((\<forall> x. P x) \<or> (\<forall> x. Q x)) \<longleftrightarrow> (\<forall> x. (P x \<or> Q x))"
proof -
  (*
    'a = {a, b}
    P(a) = False
    P(b) = True
    Q(a) = True
    Q(b) = False
  *)
oops

lemma "d":
  shows "((\<exists> x. P x) \<or> (\<exists> x. Q x)) \<longleftrightarrow> (\<exists> x. (P x \<or> P x))"
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

lemma "e":
  shows "(\<forall> x. \<exists> y. P x y) \<longrightarrow> (\<exists> y. \<forall> x. P x y)"
  (*
    'a = {a,b}
    P(a,a) = False
    P(a,b) = True
    P(b,a) = True
    P(b,b) = False
  *)
oops

lemma "f":
  shows "(\<not>(\<forall> x. P x)) \<longleftrightarrow> (\<exists> x. \<not> P x)"
proof -
  { 
    assume a: "(\<not>(\<forall> x. P x))"
    {
      assume b: "\<not>(\<exists> x. \<not> P x)"
      {
        fix y
        {
          assume c: "\<not>P y"
          from c have d: "\<exists> x. \<not> P x" by (rule exI)
          from b d have "False" by (rule notE)
        }
        from this have e: "P y" by (rule ccontr)
      }
      from this have d: "\<forall> x. P x" by (rule allI)
      from a d have "False" by (rule notE)
    }
    from this have "\<exists> x. \<not> P x" by (rule ccontr)
  } 
  note ltor = this
  {
    assume 1: "\<exists> x. \<not> P x"
    from 1 obtain a where 2: "\<not>P a" by (rule exE)
    { 
      assume 3: "\<forall> x. P x"
      from 3 have 4: "P a" by (rule allE)
      from 2 4 have "False" by (rule notE)
    } 
    from this have "\<not>(\<forall> x. P x)" by (rule notI)
  }
  note rtol = this
  from ltor rtol have "(\<not>(\<forall> x. P x)) \<longleftrightarrow> (\<exists> x. \<not> P x)" by (rule iffI)
  thus ?thesis .
qed

subsection \<open>Exercise 3\<close>

theorem "3a":
  shows "(\<exists> x. \<forall> y. P x y) \<longrightarrow> (\<forall> y. \<exists> x. P x y)"
proof -
  {
    assume a: "\<exists> x. \<forall> y. P x y"
    {
      fix y
      from a obtain x where 1: "\<forall> y. P x y" by (rule exE)
      hence "P x y" by (rule allE)
      hence "\<exists> x. P x y" by (rule exI)
    }
    hence "\<forall> y. \<exists> x. P x y" by (rule allI)
  }
  thus ?thesis by (rule impI)
qed

lemma "3f":
  shows "(\<not>(\<forall> x. P x)) \<longleftrightarrow> (\<exists> x. \<not> P x)"
proof
  assume a: "(\<not>(\<forall> x. P x))"
  show "\<exists> x. \<not> P x"
  proof (rule ccontr)
    assume b: "\<not>(\<exists> x. \<not> P x)"
    {
        fix y
        {
          assume "\<not>P y"
          hence "\<exists> x. \<not> P x" by (rule exI)
          with b have "False" by (rule notE)
        }
        hence "P y" by (rule ccontr)
      }
      hence "\<forall> x. P x" by (rule allI)
      with a show "False" by (rule notE)
  qed
next
  assume 1: "\<exists> x. \<not> P x"
  show "\<not>(\<forall> x. P x)"
  proof (rule notI)
    from 1 obtain a where 2: "\<not>P a" by (rule exE)
    assume "\<forall> x. P x"
    hence "P a" by (rule allE)
    with 2 show "False" by (rule notE)
  qed
qed

subsection \<open>Exercise 4\<close>

lemma allDeMorgan: "\<not> (\<forall> x. P(x)) \<Longrightarrow> (\<exists> x. \<not> (P(x)))" by simp

lemma
  shows a: "(\<exists> x. (D(x)) \<longrightarrow> (\<forall> y. D(y)))"
proof cases
  assume a: "\<forall> y. D(y)"  
  {
    assume "(\<exists> x. D(x))"
    from a have "(\<forall> y. D(y))" by -
  }
  from this have ?thesis by (rule impI) (* why the fuck not? *)
  thus ?thesis .
next
  assume "\<not> (\<forall> y. D(y))"
  then have "\<exists> y. \<not> (D(y))" by (rule allDeMorgan)
  from this obtain y where 3: "\<not> D(y)"
  (* if there is someone (y) who is not drinking, then D(y) \<longrightarrow> \<forall> x. D(x) is true *)
  (*
  assume D(y)
  False
  \<Rightarrow> ?Thesis (from false everything follows)
  *)
  sorry
qed

end
