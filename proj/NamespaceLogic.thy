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
  | negation F ("\<not>_")
  | conjunction F F ("_\<^bold>&_" 80)
  | separation F F ("_\<^bold>\<parallel>_" 80)
  | disclosure a ("\<section>\<acute>_`" 80)
  | dissemination a F ("_!(_)" 80)
  | reception a n F ("\<langle>_?_\<rangle>" 80)
  | greatestFixPoint F F ("rec_._" 80)
  | quantification n F F ("\<forall>_:_._")
  and a = indication F ("\<section>`_\<acute>")
  | n

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
fun evalF :: "P set \<Rightarrow> F \<Rightarrow> P set"
  and evalA :: "n set \<Rightarrow> a \<Rightarrow> n set"
  where "evalF A true = A"
    | "evalA N \<section>`\<phi>\<acute> = {x | x P. (x =N `P\<acute>) \<and> (P \<in> (evalF (toProc N) \<phi>)) \<and> (x \<in> N)}"
    | "evalF _ false = {Null}"
    | "evalF A (negation \<phi>) = A - (evalF A \<phi>)"
    | "evalF A (\<phi> \<^bold>& \<psi>) = evalF A \<phi> \<inter> evalF A \<psi>"
    | "evalF A (\<phi> \<^bold>\<parallel> \<psi>) = {p\<parallel>q | p q. p\<parallel>q \<in> A \<and> (
                      (p \<in> (evalF A \<phi>) \<and> q \<in> (evalF A \<psi>))
                    \<or> (p \<in> (evalF A \<psi>) \<and> q \<in> (evalF A \<psi>)))}"
    | "evalF A (disclosure a) = {P | P x. ((P \<equiv>\<alpha> \<acute>x`) \<and> (P \<in> A) \<and> (x \<in> (evalA (toNames A) a)))}" 
    | "evalF A (dissemination a P) = {P | P Q x. (P \<equiv>\<alpha> (x\<triangleleft>Q\<triangleright>)) \<and> (P \<in> A) \<and> (Q \<in> A) \<and> (x \<in> (evalA (toNames A) a))}"
    | "evalF A (reception a b \<phi>) = 
    {P | P Q x y z c. (P \<equiv>\<alpha> (y\<leftarrow>x. Q.)) \<and> (Q{z\<setminus>y} \<in> {R{c\<setminus>b} | R. R \<in> (evalF A \<phi>)})
    \<and> (P \<in> A) \<and> (y \<in> toNames A) \<and> (c \<in> toNames A) \<and> (z \<in> toNames A)}"
    | "evalF A (quantification a \<phi> F) = {P{x\<setminus>a} | P x. (x \<in> (evalA (toNames A) \<section>`\<phi>\<acute>)) \<and> (P \<in> A)}" 
end