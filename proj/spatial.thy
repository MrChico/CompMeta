theory spatial
imports Main
begin

(*The mutually recursive datatypes of processes and names*)
datatype P = Null             ("\<^bold>0")
           | input n n P      ("_\<leftarrow>_._" 60)
           | lift n P         ("_\<triangleleft>_\<triangleright>" 20)
           | drop n           ("\<acute>_`" 30)
           | par P P          (infixl "\<parallel>" 53)    
     and n = quote P          ("`_\<acute>")

abbreviation Output :: "n \<Rightarrow> n \<Rightarrow> P" ("_[_]")
  where "Output x y \<equiv> x\<triangleleft>\<acute>y`\<triangleright>"

abbreviation zero :: n
  where "zero \<equiv> `\<^bold>0\<acute>"


value "zero \<leftarrow> zero.\<^bold>0"
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"

abbreviation congru :: "P \<Rightarrow> P \<Rightarrow> bool" (infix "=C" 42)
  where "congru \<equiv> \<lambda> p q. p = q 
  \<or> ((p \<parallel> \<^bold>0) = q) 
  \<or> (\<^bold>0 \<parallel> p  = q)
  \<or> (p = (q \<parallel> \<^bold>0))
  \<or> (p = (\<^bold>0 \<parallel> q))
  \<or> (\<exists> x y. (p = x \<parallel> y) \<and> (q = y \<parallel> x))
  \<or> (\<exists> x y z. (p = (x \<parallel> y) \<parallel> z) \<and> (q = y \<parallel> (x \<parallel> z)))"
value "(Null \<parallel> Null) =C Null"
(*
quotient_type congr = "P \<Rightarrow> P \<Rightarrow> bool" (infix "=C" 42)
  where "((P \<parallel> \<^bold>0) =C P)= true"
  | "((\<^bold>0 \<parallel> P) =C P)= true"
*)
consts conguence :: "P \<Rightarrow> P \<Rightarrow> bool" (infix "=C" 42)

abbreviation reflexive
  where "reflexive \<equiv> \<forall> r. r =C r"
abbreviation transitive
  where "transitive \<equiv> \<forall> x. \<forall> y. \<forall> z. x =C y \<and> y =C z \<longrightarrow> x =C z"
abbreviation symmetric
  where "symmetric \<equiv> \<forall> x. \<forall> y. x =C y \<longrightarrow> y =C x"
abbreviation Id 
  where "Id \<equiv> \<forall> p. (\<^bold>0 \<parallel> p) =C p"
abbreviation Sym
  where "Sym \<equiv> \<forall> p. \<forall> q. p \<parallel> q =C q \<parallel> p"
abbreviation Assoc
  where "Assoc \<equiv> \<forall> p. \<forall> q. \<forall> r. (p \<parallel> q) \<parallel> r =C p \<parallel> (q \<parallel> r)"

axiomatization where leastConguence: "reflexive \<and> transitive \<and> symmetric \<and> Id \<and> Sym \<and> Assoc"

quotient_type congre = "P set" / "leastCongruence" 

theorem test:
  shows "\<forall> p.(p \<parallel> \<^bold>0) =C p"
using leastConguence by blast
(*
theorem testtie:
  shows "p \<parallel> (\<^bold>0 \<parallel> q) =C q \<parallel> p"  
by (metis leastConguence)
*)
abbreviation nEq :: "n \<Rightarrow> n \<Rightarrow> bool" (infix "=N" 42)
  where "nEq \<equiv> \<lambda> x y . `\<acute>y`\<acute> = x \<or> `\<acute>x`\<acute> = y \<or> (\<exists> z1::P . \<exists> z2::P. `z1\<acute> = x \<and> `z2\<acute> = y \<and> z1 =C z2)"

(*Name equivalence*)
(*
consts nameEq :: "n \<Rightarrow> n \<Rightarrow> bool" (infix "=N" 42)
abbreviation QuoteDrop
  where "QuoteDrop \<equiv> \<forall>x. `\<acute>x`\<acute> =N x"
abbreviation StructEquiv
  where "StructEquiv \<equiv> \<forall>p q. p =C q \<longrightarrow> `p\<acute> =N `q\<acute>"
abbreviation reflexiveN
  where "reflexiveN \<equiv> \<forall> r. r =N r"
abbreviation transitiveN
  where "transitiveN \<equiv> \<forall> x. \<forall> y. \<forall> z. x =N y \<and> y =N z \<longrightarrow> x =N z"
abbreviation symmetricN
  where "symmetricN \<equiv> \<forall> x. \<forall> y. x =N y \<longrightarrow> y =N x"

axiomatization where name_equivalence: "QuoteDrop \<and> StructEquiv \<and> reflexiveN \<and> transitiveN \<and> symmetricN"
*)

abbreviation reflexiveR
  where "reflexiveR \<equiv> \<lambda> R. \<forall> r. R r r"
abbreviation transitiveR
  where "transitiveR \<equiv> \<lambda> R. \<forall> x. \<forall> y. \<forall> z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation symmetricR
  where "symmetricR \<equiv> \<lambda> R. \<forall> x. \<forall> y. R x y \<longrightarrow> R y x"

theorem name_congruence_reflexive:
  shows "reflexiveR nEq"
by (metis leastConguence n.exhaust)

theorem name_congruence_symmetric:
  shows "symmetricR nEq"
using leastConguence by blast

theorem name_congruence_transitive:
  shows "transitiveR nEq"


value "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"

theorem testerr:
  shows "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"
by (metis leastConguence)


(*Gives the set of free names in a process*)
fun free :: "P \<Rightarrow> n set" where
  "free \<^bold>0 = {}"
  | "free (x \<leftarrow> y . P) = {x} \<union> (free(P) - {y})"
  | "free (x \<triangleleft> P \<triangleright>) = {x} \<union> free P"
  | "free (P \<parallel> Q) = free P \<union> free Q"
  | "free (\<acute>x`) = {x}"

(*Gives the set of bound names in a process*)
fun bound :: "P \<Rightarrow> n set" where
  "bound \<^bold>0 = {}"
  | "bound (x \<leftarrow> y . P) = {y} \<union> bound(P)"
  | "bound (x \<triangleleft> P \<triangleright>) = bound P"
  | "bound (P \<parallel> Q) = bound P \<union> bound Q"
  | "bound (\<acute>x`) = {}"

(*Names occurring in a process*)
fun names :: "P \<Rightarrow> n set"
  where "names P = free(P) \<union> bound(P)"
(*quote depth*)
function n_depth :: "n \<Rightarrow> nat" ("#" 60) 
  and P_depth :: "P \<Rightarrow> nat" ("#" 60)
  where
  "n_depth `P\<acute> = 1 + (P_depth P)"
  | "P_depth P = (if (names P \<noteq> {}) then Max({ ( n_depth x ) | x. x \<in> (names P)}) else 0)"
  apply pat_completeness
  apply blast
  apply simp
  by blast
termination
  sorry  (*Even without termination proof, we can use the n_depth/P_depth function*)

value "P_depth (\<acute>zero`)"

fun newName :: "nat \<Rightarrow> n"
  where "newName 0 = `\<^bold>0\<acute>"
       |"newName (Suc n) = `(Output (newName n) (newName n))\<acute>"

abbreviation one :: n
  where "one \<equiv> newName 1"
abbreviation two :: n
  where "two \<equiv> newName 2"
abbreviation three :: n
  where "three \<equiv> newName 3"


(*substitution*)
(*Takes a process, specifies the names to be substituted and returns a process*)
abbreviation sn :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n" where
  "sn x q p \<equiv> (if (x =N p) then q else x)" 

value "(sn zero zero zero)"
value "newName (Max ({(n_depth zero), 0::nat}))"

(*with z = (newName (P_depth(R)))*)
abbreviation z
  where "z \<equiv> \<lambda> q::n.  \<lambda> p::n. \<lambda> R::P. newName (Max({(n_depth(q)), (P_depth(R)), (n_depth(p)) }))"
  

function s :: "P \<Rightarrow> n \<Rightarrow> n \<Rightarrow> P" ("(_) {_\<setminus>_}" 52)
where "(\<^bold>0){_\<setminus>_}             = \<^bold>0"
   | "(R \<parallel> S){q\<setminus>p}          = ((R){q\<setminus>p}) \<parallel> ((S){q\<setminus>p})" 
   | "( x \<leftarrow> y . R){q\<setminus>p}    = ((sn x q p) \<leftarrow> (z q p R)  . ((R {(z q p R)\<setminus>y}){q\<setminus>p}))"  
   | "( x\<triangleleft>R\<triangleright>) {q\<setminus>p}         = R"
   | "(\<acute>x`){q\<setminus>p}            = (if x =N p then \<acute>q` else \<acute>x`)"
sorry
termination
sorry

value "\<^bold>0{zero\<setminus>zero}"
value "\<acute>zero` {two\<setminus> zero}"
value "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero }"

theorem testerrr:
shows "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero } = (\<^bold>0 \<parallel> (\<acute>(newName 2)`))"
by (simp add: leastConguence name_equivalence)

end