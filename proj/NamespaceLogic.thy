theory NamespaceLogic
imports RhoCalc NameEquiv Substitution Dynamics Main
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
  (*| greatestFixPoint nat F ("rec _._" 80)
  | quantification n F F ("\<forall>_:_._")*)
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
  where "valuation F a b \<equiv> if (a) = "
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
    | "evalF (\<acute>`P\<acute>`) (\<phi> \<^bold>\<parallel> \<psi>) = evalF P (\<phi> \<^bold>\<parallel> \<psi>)"
    | "evalF p (disclosure a) = (evalA `p\<acute> (name a))" (*Again, almost. Should be up to \<alpha>-equivalence*)
    | "evalF (x\<triangleleft>P\<triangleright>) (dissemination a \<phi>) = ((evalA x a) \<and> (evalF P \<phi>))"
    (*remaining cases false*)
    | "evalF Null (dissemination a \<phi>) = False"
    | "evalF (x\<leftarrow>y. P .) (dissemination a \<phi>) = False"
    | "evalF (\<acute>`P\<acute>`) (dissemination a \<phi>) = evalF P (dissemination a \<phi>)"
    | "evalF (P\<parallel>Q) (dissemination a \<phi>) = ((evalF P (dissemination a \<phi>) \<and> (Q =C Null))
    \<or> (evalF Q (dissemination a \<phi>) \<and> (P =C Null)))"
    (*The last cases are difficult, because Meredith has not defined substitution on formulae*)
    | "evalF (x\<leftarrow>y . P.) (reception a `Q\<acute> \<phi>) = ((evalA y a) \<and> (evalF (P{`Q\<acute>\<setminus>x}) \<phi>))"
    (*Remaining cases false*)
    | "evalF Null (reception a `Q\<acute> \<phi>) = False"
    | "evalF (x\<triangleleft>P\<triangleright>) (reception a `Q\<acute> \<phi>) = False"
    | "evalF (\<acute>`P\<acute>`) (reception a `Q\<acute> \<phi>) = evalF P (reception a `Q\<acute> \<phi>)"
    | "evalF (P\<parallel>R) (reception a `Q\<acute> \<phi>) = ((evalF P (reception a `Q\<acute> \<phi>) \<and> (R =C Null))
    \<or> (evalF R (reception a `Q\<acute> \<phi>) \<and> (P =C Null)))"
apply pat_completeness by auto
termination by lexicographic_order

subsection\<open>Example\<close>
text\<open>A process witnessing the following formula satisfies the condition that it does not take input
on any other name than 'one':\<close>

abbreviation oneA :: "a" where "oneA \<equiv> name one"
abbreviation onlyOne :: "a" where "onlyOne \<equiv> (\<section>` (\<section>\<acute>one`)  \<acute>)"

value "evalA one oneA"
value "evalA one onlyOne" 
abbreviation onlyOnOne :: "F" where "onlyOnOne \<equiv> ((\<langle> (name one) ? zero \<rangle>) true)"

text\<open>The process \<psi> witnesses onlyOnOne\<close>
theorem psiOnOne:
shows "evalF (one\<leftarrow>one . Zero .) onlyOnOne"
by simp

end