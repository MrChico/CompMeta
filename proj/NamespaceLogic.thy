theory NamespaceLogic
imports RhoCalc NameEquiv Substitution Dynamics
begin

section\<open>Namespace logic\<close>
text\<open>The logic of the rho-calculus closely mimics the structure of our processes, in order to be
able to express things such as: this process only takes input over these channels throughout its 
lifetime. Since names are simply quoted processes, this logic is called namespace logic.
We begin by the datatype of the constructible formulae of namespace logic:\<close>
datatype F = true
  | false
  | negation F ("\<^bold>\<not>_")
  | conjunction F F ("_\<^bold>&_" 80)
  | separation F F ("_\<^bold>\<parallel>_" 80)
  | disclosure n ("\<section>\<acute>_`" 80)
  | dissemination a F ("_!(_)" 80)
  | reception a n F ("\<langle>_?_\<rangle>" 80)
 (* | greatestFixPoint F F ("rec _._" 80)*)
  | quantification n F F ("\<forall>_:_._")
  and a = indication F ("\<section>`_\<acute>")
  | name n

section\<open>Semantics\<close>
text\<open>Instead of evaluating formulae to truth values, we ask for which processes or names 
satisfy the given formula. In other words, to evaluate a formula we give it a candidate set of 
processes, and then we are returned the set of processes 'witnessing' the formula.\<close>
(*turns a set of processes to a set of names*)
abbreviation toNames :: "P set \<Rightarrow> n set"
  where "toNames A \<equiv> {`x\<acute> | x. x \<in> A}"

abbreviation toProc :: "n set \<Rightarrow> P set"
  where "toProc A \<equiv> {\<acute>x` | x. x \<in> A}"
(*
fun valuation :: "F \<Rightarrow> a \<Rightarrow> a \<Rightarrow> F"
  where "valuation F a b \<equiv> if (a)"
*)
(*Evaluate formulae by checking which processes witness them
WIP*)
(*In this approach evalF serves as the characteristic function
for the set of processes that satisfy a certain formula F*)
function evalF :: "P \<Rightarrow> F \<Rightarrow> bool"
  and evalA :: "n \<Rightarrow> a \<Rightarrow> bool"
  where "evalF p true = True"
    | "evalF _ false = False"
    | "evalF p (\<^bold>\<not> \<phi>) = (\<not>(evalF p \<phi>))"
    | "evalA `P\<acute> \<section>`\<phi>\<acute> = (evalF P \<phi>)" (*almost this, should be P up to name equality*)
    | "evalA n (name `P\<acute>) = n =N `P\<acute>"
    | "evalF p (\<phi> \<^bold>& \<psi>) = (evalF p \<phi> \<and> evalF p \<psi>)"
    | "evalF (P\<parallel>Q) (\<phi> \<^bold>\<parallel> \<psi>) = (((evalF P \<phi>) \<and> (evalF Q \<psi>)) \<or>
    ((evalF Q \<phi>) \<and> (evalF P \<psi>)))"
    (*false for all other cases*)
    | "evalF Null (\<phi> \<^bold>\<parallel> \<psi>) = False"
    | "evalF (x \<leftarrow> y . P .)  (\<phi> \<^bold>\<parallel> \<psi>) = False"
    | "evalF (x\<triangleleft>P\<triangleright>) (\<phi> \<^bold>\<parallel> \<psi>) = False"
    | "evalF (\<acute>n`) (\<phi> \<^bold>\<parallel> \<psi>) = False"
    | "evalF p (disclosure a) = (evalA `p\<acute> (name a))" (*Again, almost. Should be up to \<alpha>-equivalence*)
    | "evalF (x\<triangleleft>P\<triangleright>) (dissemination a \<phi>) = ((evalA x a) \<and> (evalF P \<phi>))"
    (*remaining cases false*)
    | "evalF Null (dissemination a \<phi>) = False"
    | "evalF (x\<leftarrow>y. P .) (dissemination a \<phi>) = False"
    | "evalF (\<acute>`P\<acute>`) (dissemination a \<phi>) = evalF P (dissemination a \<phi>)"
    | "evalF (P\<parallel>Q) (dissemination a \<phi>) = ((evalF P (dissemination a \<phi>) \<and> (Q =C Null))
    \<or> (evalF Q (dissemination a \<phi>) \<and> (P =C Null)))"
    (*The last cases are difficult, because we have to define that substitution on formulae*)
(*    | "evalF (x\<leftarrow>y . P.) (reception a b \<phi>) = (evalF P \<phi>)"
    {P | P Q x y z c. (P \<equiv>\<alpha> (y\<leftarrow>x. Q.)) \<and> (Q{z\<setminus>y} \<in> {R{c\<setminus>b} | R. R \<in> (evalF A \<phi>)})
    \<and> (P \<in> A) \<and> (y \<in> toNames A) \<and> (c \<in> toNames A) \<and> (z \<in> toNames A)}"
   (* | "evalF A (quantification a \<phi> F) = {P{x\<setminus>a} | P x. (x \<in> (evalA (toNames A) \<section>`\<phi>\<acute>)) \<and> (P \<in> A)}" 
    | "evalF A (rec X. \<phi>) = undefined"*)
apply pat_completeness
by auto
termination
sorry
*)
(*
function evalF :: "P set \<Rightarrow> F \<Rightarrow> P set"
  and evalA :: "n set \<Rightarrow> a \<Rightarrow> n set"
  where "evalF A true = A"
    | "evalA N \<section>`\<phi>\<acute> = {x | x P. (x =N `P\<acute>) \<and> (P \<in> (evalF (toProc N) \<phi>)) \<and> (x \<in> N)}"
    | "evalA N (name `P\<acute>) = {x. (x \<in> N) \<and> (x =N `P\<acute>)}"
    | "evalF _ false = {Null}"
    | "evalF A (negation \<phi>) = A - (evalF A \<phi>)"
    | "evalF A (\<phi> \<^bold>& \<psi>) = evalF A \<phi> \<inter> evalF A \<psi>"
    | "evalF A (\<phi> \<^bold>\<parallel> \<psi>) = {p\<parallel>q | p q. p\<parallel>q \<in> A \<and> (
                      (p \<in> (evalF A \<phi>) \<and> q \<in> (evalF A \<psi>))
                    \<or> (p \<in> (evalF A \<psi>) \<and> q \<in> (evalF A \<psi>)))}"
    | "evalF A (disclosure a) = {P | P x. ((P \<equiv>\<alpha> \<acute>x`) \<and> (P \<in> A) \<and> (x \<in> (evalA (toNames A) (name a))))}" 
    | "evalF A (dissemination a P) = {P | P Q x. (P \<equiv>\<alpha> (x\<triangleleft>Q\<triangleright>)) \<and> (P \<in> A) \<and> (Q \<in> A) \<and> (x \<in> (evalA (toNames A) a))}"
    | "evalF A (reception a b \<phi>) = 
    {P | P Q x y z c. (P \<equiv>\<alpha> (y\<leftarrow>x. Q.)) \<and> (Q{z\<setminus>y} \<in> {R{c\<setminus>b} | R. R \<in> (evalF A \<phi>)})
    \<and> (P \<in> A) \<and> (y \<in> toNames A) \<and> (c \<in> toNames A) \<and> (z \<in> toNames A)}"
    | "evalF A (quantification a \<phi> F) = {P{x\<setminus>a} | P x. (x \<in> (evalA (toNames A) \<section>`\<phi>\<acute>)) \<and> (P \<in> A)}" 
(*    | "evalF A (rec X. \<phi>) = undefined"*)
apply pat_completeness
by auto
termination
sorry
*)
subsection\<open>Example\<close>
text\<open>A process witnessing the following formula satisfies the condition that it does not take input
on any other name than 'one':\<close>

abbreviation oneA :: "a" where "oneA \<equiv> name one"
abbreviation onlyOne :: "a" where "onlyOne \<equiv> (\<section>` (\<section>\<acute>one`)  \<acute>)"

value "evalA {zero, one, two} oneA"
value "evalA {zero, one, two} onlyOne" 
abbreviation onlyOnOne :: "F" where "onlyOnOne \<equiv> ((\<langle>  (\<section>` \<section>\<acute>one`  \<acute>) ? b \<rangle>) true)  & (\<not>\<langle>(\<not>\<section>\<acute>one`)? b \<rangle>true)"

end