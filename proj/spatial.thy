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

theorem testtie:
  shows "p \<parallel> (\<^bold>0 \<parallel> q) =C q \<parallel> p"  
by (metis leastConguence)

(*Name equivalence*)
fun nameEq :: "n \<Rightarrow> n \<Rightarrow> bool" (infix "=N" 42)
  where "nameEq `\<acute>x`\<acute> x = (x = x)"
  | "nameEq `P\<acute> `Q\<acute>= (P =C Q)" 
abbreviation QuoteDrop
  where "QuoteDrop \<equiv> \<forall>x. `\<acute>x`\<acute> =N x"
abbreviation StructEquiv
  where "StructEquiv \<equiv> \<forall>p q. p =C q \<longrightarrow> `p\<acute> =N `q\<acute>"

axiomatization where name_equivalence: "QuoteDrop \<and> StructEquiv"

theorem testerr:
shows "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"
by (meson leastConguence name_equivalence)

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
  (*apply lexicographic_order*)
  sorry
  (*
  apply (relation "measure (\<lambda>x. 2)")
  apply simp
  apply (induct _ rule: n.induct)
  by (simp add: name_equivalence)

  apply simp
  apply simp
  apply simp
  apply 
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  sledgehammer
  sledgehammer
  sorry  (*Even without termination proof, we can use the n_depth/P_depth function*)
*)
(*---Substitution---*)
(*Takes a process, specifies the names to be substituted and returns a process*)
abbreviation sn :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n" where
  "sn x q p \<equiv> (if (x =N p) then q else x)" 

function s :: "P \<Rightarrow> n \<Rightarrow> n \<Rightarrow> P" ("(_) {_\<setminus>_}" 52)
where "(\<^bold>0){_\<setminus>_}             = \<^bold>0"
   | "(R \<parallel> S){q\<setminus>p}          = ((R){q\<setminus>p}) \<parallel> ((S){q\<setminus>p})" 
   | "( x \<leftarrow> y . R){q\<setminus>p}    = ((sn x q p) \<leftarrow> z . ((R {z\<setminus>y}){q\<setminus>p}))" 
   | "( x\<triangleleft>R\<triangleright>) {q\<setminus>p}         = R"
   | "(\<acute>x`){q\<setminus>p}            = (\<acute>x`)"
(*
  "s x\<leftarrow>y.R q p = (sn x q p)\<leftarrow>z.(s ((s R z y) q p))" 
*)
end