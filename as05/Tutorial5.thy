section "Playing with HOL"

theory Tutorial5
imports Main 

begin
(*<*)
text "Ignore this"
no_notation
  subset  ("op \<subset>") and
  subset  ("(_/ \<subset> _)" [51, 51] 50) and
  subset_eq  ("op \<subseteq>") and
  subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) 

no_notation
  union (infixl "\<union>" 65) and
  inter (infixl "\<inter>" 70)

no_notation
  Set.member  ("op \<in>") and
  Set.member  ("(_/ \<in> _)" [51, 51] 50)
text "Ignore this END"
(*>*)


subsection "Sets"

text \<open>In the context of HOL, a set @{term "A"} can be defined using
      its characteristic function @{term "\<chi>\<^sub>A"}:
      For a set @{term "A"} of objects of type @{text "'a"},
      an object @{term "x :: 'a"} is an element of @{term "A"}
      if and only if @{term "\<chi>\<^sub>A x"} holds
      (i.e. @{term "\<chi>\<^sub>A"} represents
      the extension of the set @{term "A"} when interpreted as a predicate).

      Speaking in HOL terms, the
      char. function @{term "\<chi>\<^sub>A"} is a term of type @{text "'a \<Rightarrow> bool"}.\<close>

type_synonym 'a Set = "'a \<Rightarrow> bool"



paragraph "Constructing sets"

term "\<lambda>x. P x" -- "set of objects for which P holds"



paragraph "Membership"
text \<open>Membership of a set can easily defined as application to the characteristic
      function.\<close>

definition member :: "'a \<Rightarrow> 'a Set \<Rightarrow> bool" (infix "\<in>" 42) where
  "x \<in> A \<equiv> A x"



paragraph "Other operators on sets"

text "Define intersection by"
abbreviation intersect :: "'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" (infix "\<inter>" 41) where
  "A \<inter> B \<equiv> \<lambda> x. A x \<and> B x"

text "Define union by"
abbreviation union :: "'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" (infix "\<union>" 41) where
  "A \<union> B \<equiv> \<lambda> x. A x \<or> B x"

text "Define difference by"
abbreviation diff :: "'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" (infix "\<setminus>" 41) where
  "A \<setminus> B \<equiv> \<lambda> x. A x \<and> \<not> B x"

text "Define subset by"
abbreviation subset :: "'a Set \<Rightarrow> 'a Set \<Rightarrow> bool" (infix "\<subseteq>" 41) where
  "A \<subseteq> B \<equiv> \<forall> x. A x \<longrightarrow> B x"

text "Define intersection by"
abbreviation setequiv :: "'a Set \<Rightarrow> 'a Set \<Rightarrow> bool" (infix "\<simeq>" 41) where
  "A \<simeq> B \<equiv> \<forall> x. A x \<longleftrightarrow> B x"






subsection "Relations"

text \<open>As for sets, we can define relations in HOL.
      A relation @{term "R"} can be modeled by a term @{term "R"}
      of type @{text "'a \<Rightarrow> 'a \<Rightarrow> bool"}.
       
     Then, for two objects @{term "x :: 'a"}, @{term "y :: 'a"}
     @{term "x"} is in relation to @{term "y"}, infix-ly written @{term "xRy"},
     if and only if @{term "R x y"} holds.\<close>



text \<open>
\<^enum> Formulate a predicate that is true iff a given relation
        @{term "R :: 'a \<Rightarrow> 'a \<Rightarrow> bool"} is reflexive.
\<^enum> Formulate a predicate that is true iff a given relation
        @{term "R :: 'a \<Rightarrow> 'a \<Rightarrow> bool"} is transitive.
\<^enum> Formulate a predicate that is true iff a given relation
        @{term "R :: 'a \<Rightarrow> 'a \<Rightarrow> bool"} is symmetric.
\<^enum> Formulate a predicate that is true iff a given relation
        @{term "R :: 'a \<Rightarrow> 'a \<Rightarrow> bool"} is an equivalence relation.
\<^enum> Formulate a predicate that is true iff a given relation.
        @{term "R :: 'a \<Rightarrow> 'a \<Rightarrow> bool"} is a total order.
\<close>

type_synonym 'a Rel = "'a \<Rightarrow> 'a \<Rightarrow> bool"

abbreviation reflexive :: "'a Rel \<Rightarrow> bool" where
  "reflexive R \<equiv> \<forall> A. R A A"

abbreviation transitive :: "'a Rel \<Rightarrow> bool" where
  "transitive R \<equiv> \<forall> A. \<forall> B. \<forall> C. R A B \<and> R B C \<longrightarrow> R A C"

abbreviation symmetric :: "'a Rel \<Rightarrow> bool" where
  "symmetric R \<equiv> \<forall> A. \<forall> B. R A B \<longrightarrow> R B A"

abbreviation equivalence :: "'a Rel \<Rightarrow> bool" where
  "equivalence R \<equiv> reflexive R \<and> transitive R \<and> symmetric R"

abbreviation totalOrder :: "'A Rel \<Rightarrow> bool" where
  "totalOrder R \<equiv> reflexive R \<and> transitive R \<and> \<not> symmetric R \<and> (\<forall> A. \<forall> B. R A B \<or> R B A)"


text \<open>
Bonus-task (harder):
\<^enum> Formulate a function that returns the reflexive closure
        of a relation  @{term "R :: 'a \<Rightarrow> 'a \<Rightarrow> bool"}.
\<^enum> Formulate a function that returns the transitive closure
        of a relation  @{term "R :: 'a \<Rightarrow> 'a \<Rightarrow> bool"}.
\<close> 
fun reflexclosure :: "'a Rel \<Rightarrow> 'a Rel" where
  "reflexclosure R = (\<lambda> x. \<lambda> y. R x y \<or> x = y)"

fun transitiveclosure :: "'a Rel \<Rightarrow> 'a Rel" where
(*
  "transitiveclosure = (\<lambda> x. \<lambda> y. R x y \<or> (\<exists> z. (transitiveclosure R) x z \<and> (transitiveclosure R) z y))"
*)
  "transitiveclosure = (\<lambda> x. \<lambda> y. \<forall> S. transitive S \<rightarrow> ((\<forall> a. \<forall> b. R a b \<longrightarrow> S a b) \<longrightarrow> S x y))"

(* term "(op =) b" *)

text "You can verify your definitions using by proving:"

lemma "\<forall>R. trans (transclosure R)" oops
lemma "\<forall>R. \<forall>x. \<forall>y. R x y \<longrightarrow> (transclosure R) x y" oops

end