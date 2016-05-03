section \<open>Example theory file for getting acquainted with Isabelle\<close>
(*<*)
theory Example
imports Main

begin
(*>*)
subsection \<open>Terms\<close>
text \<open>
  We can write logical formulae and terms in the usual notation.
  Connectives such as @{text "\<not>"},@{text "\<or>"}, @{text "\<and>"} etc. can be typed using the backslash
  @{text "\\"} followed by the name of the sign. I.e. @{text "\\not"} for @{text "\<not>"}.
  Note that during typing @{text "\\not"} at some point there will be a pop-up menu
  offering you certain auto completion suggestions that you can accept by
  pressing the tab key.
\<close>

subsection \<open>Types\<close>
text \<open>
  All terms (and also constant symbols, variables etc.) are associated
  a type. The type @{type "bool"} is the type of all Boolean-values objects
  (e.g. truth values).
  New types can be inserted at will.
\<close>

typedecl "i" -- "Create a new type i for the type of individuals"

subsection \<open>Constants\<close>
text \<open>
  New constants can be defined using the @{text "consts"} keyword.
  You need to specify the type of the constant explicitly.
\<close>
subsection \<open>Terms and Formulas\<close>
text \<open>
  In higher-order logic (HOL), terms are all well-formed expressions
  that can be expressed within the logic. A term has a unique type, such
  as in @{term "f(A) :: i"} where the term @{term "f(A)"} has type
  @{type "i"}. Terms of type @{type "bool"} are called "formulas".
\<close>

subsubsection \<open>Example formula 1\<close>
text \<open>If it's raining the street will get wet\<close>

consts raining :: "bool" -- "constant symbol for raining"
consts wet :: "i \<Rightarrow> bool" -- "predicate symbol for wet"
consts street :: "i" -- "constant symbol for the street"

prop "raining \<longrightarrow> wet(street)" -- "raining implies street-is-wet"
prop "wet(street) \<longrightarrow> raining" 

subsubsection \<open>Example formula 2\<close>
consts good :: "i \<Rightarrow> bool" -- "predicate symbol for being good"

prop "good(A)" -- "A is good"
text \<open>A is a free variable of the above term, hence it is not closed\<close>

subsubsection \<open>Example formula 3\<close>

prop "\<forall>A. good(A)" -- "everything is good"
text \<open>A is a a bound variable of the above term, which is universally qualified.\<close>


subsection \<open>Proofs\<close>
text \<open>We will learn how to formalize proofs in Isabelle throughout this course.\<close>

subsubsection \<open>Proofs with handy keywords\<close>

theorem MyFirstTheorem:
  assumes "A"
  shows "B \<longrightarrow> A"
proof -
  {
    assume "B"
    from assms have "A" by - -- "Iterate the fact that A holds by assumptions using the - sign"
  }
  then have "B \<longrightarrow> A" by (rule impI)
  thus ?thesis .
qed

(*
theorem MySecondTheorem:
  shows "((A \<longrightarrow> B) \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
proof -
  {
  assume "(A \<longrightarrow> B) \<longrightarrow> C"
  assume "(A \<longrightarrow> B)"
*)
subsubsection \<open>Proofs with labels\<close>

theorem ExcludedMiddle:
 shows "A \<or> \<not> A"
 proof -
   {
      assume 1: "\<not> (A \<or> \<not> A)"
      {
        assume 2: "\<not> A"
        from 2 have 3: "A \<or> \<not> A" by (rule disjI2)
        from 1 3 have 4: "False" by (rule notE)
      } note 5=this
      from 5 have 6: "A" by (rule ccontr)
      from 6 have 7: "A \<or> \<not> A" by (rule disjI1)
      from 1 7 have "False" by (rule notE)
   }
   from this have "A \<or> \<not> A" by (rule ccontr)
   thus ?thesis .
 qed

theorem Exm2:
  shows "A \<or> \<not> A"
by simp

(*
theorem MyFirstTheorem2:
  assumes 1: "A"
  shows "B \<longrightarrow> A"
proof -
  {
    assume "B"
    from 1 have "A" by -
  } note 2 = this
  from 2 have "B \<longrightarrow> A" by (rule impI)
  thus ?thesis .
qed
*)

subsubsection \<open>Using the proofs\<close>
text \<open>
  We can now derive simple facts of the above theorem.
\<close>

corollary ThatFollowsDirectly:
  assumes "A"
  shows "P(A) \<longrightarrow> A"
using assms by (rule MyFirstTheorem[where B = "P(A)"])

subsection \<open>Exercise 1 \<close>
consts ship :: "i"
consts isBlue :: "i \<Rightarrow> bool"
consts isHuge :: "i \<Rightarrow> bool"

prop "isHuge(ship) \<and> isBlue(ship)"

consts I :: "i"
consts SunShining :: "bool"
consts Sad :: "i \<Rightarrow> bool"

prop "\<not>SunShining \<longrightarrow> Sad(I)"

consts isRaining :: "bool"

prop "isRaining \<and> \<not> isRaining"

consts going :: "i \<Rightarrow> bool"
consts she :: "i"

prop "going(I) \<longleftrightarrow> going(she)"

consts lovesIceCream :: "i \<Rightarrow> bool"
consts lovesChocolate :: "i \<Rightarrow> bool"

prop "\<forall>i.(lovesIceCream(i)\<or>lovesChocolate(i))"

prop "\<exists>i.(lovesIceCream(i)\<and>lovesChocolate(i))"

consts CanPlayTogether :: "i \<times> i \<Rightarrow> bool"

prop "\<forall>x.\<exists>y.(CanPlayTogether(x, y))" 

consts isMean :: "i \<Rightarrow> bool"

prop "\<forall>x. isMean(x) \<longrightarrow> \<not> (\<exists>y. CanPlayTogether(x, y))"

consts isDog :: "i \<Rightarrow> bool"
consts isCat :: "i \<Rightarrow> bool"
consts annoying :: "(i \<Rightarrow> bool) \<Rightarrow> bool"

prop "\<forall>P. annoying(P) \<longrightarrow> ((\<forall>x. isCat(x) \<and> P(x)) \<longleftrightarrow> (\<forall>y. isDog(y) \<and> P(y)))"

subsection \<open>Exercise 2\<close>

theorem a:
  assumes 1: "A \<and> B \<longrightarrow> C" and
  2: "B \<longrightarrow> A" and
  3: "B"
  shows "C"
  proof -
    from 2 3 have 4: "A" by (rule mp)
    from 4 3 have 5: "A \<and> B" by (rule conjI)
    from 1 5 have "C" by (rule mp)
  thus ?thesis .
qed

theorem b: 
  assumes 1: "A"
  shows "B \<longrightarrow> A"
  proof - 
    {
      assume B
      from assms have "A" by -
    } 
    from this have "B \<longrightarrow> A" by (rule impI)
  thus ?thesis .
qed

theorem c:
  assumes 1: "A \<longrightarrow> (B \<longrightarrow> C)"
  shows "B \<longrightarrow> (A \<longrightarrow> C)"
  proof - 
    {
      assume 2: "B"
      {
        assume 3: "A"
        from 1 3 have 4: "B \<longrightarrow> C" by (rule mp)
        from 4 2 have "C" by (rule mp)
      }
      from this have "A \<longrightarrow> C" by (rule impI)
    }
    from this have "B \<longrightarrow> (A \<longrightarrow> C)" by (rule impI)
    thus ?thesis .
qed

theorem d:
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

theorem e:
 shows "A \<or> \<not> A"
 proof -
   {
      assume 1: "\<not> (A \<or> \<not> A)"
      {
        assume 2: "\<not> A"
        from 2 have 3: "A \<or> \<not> A" by (rule disjI2)
        from 1 3 have 4: "False" by (rule notE)
      } note 5=this
      from 5 have 6: "A" by (rule ccontr)
      from 6 have 7: "A \<or> \<not> A" by (rule disjI1)
      from 1 7 have "False" by (rule notE)
   }
   from this have "A \<or> \<not> A" by (rule ccontr)
   thus ?thesis .
 qed


(*<*)
end
(*>*)