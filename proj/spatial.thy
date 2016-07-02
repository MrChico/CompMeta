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

abbreviation sugger :: "n \<Rightarrow> n \<Rightarrow> P" ("_[_]")
  where "sugger x y \<equiv> x\<triangleleft>\<acute>y`\<triangleright>"

abbreviation zero :: n
  where "zero \<equiv> `\<^bold>0\<acute>"

value "zero \<leftarrow> zero.\<^bold>0"
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"


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

theorem test:
  shows "\<forall> p.(p \<parallel> \<^bold>0) =C p"
using leastConguence by blast

theorem testtie:
  shows "p \<parallel> (\<^bold>0 \<parallel> q) =C q \<parallel> p"  
by (metis leastConguence)

(*Name equivalence*)
consts nameEq :: "n \<Rightarrow> n \<Rightarrow> bool" (infix "=N" 42)
abbreviation QuoteDrop
  where "QuoteDrop \<equiv> \<forall>x. `\<acute>x`\<acute> =N x"
abbreviation StructEquiv
  where "StructEquiv \<equiv> \<forall>p q. p =C q \<longrightarrow> `p\<acute> =N `q\<acute>"

axiomatization where name_equivalence: "QuoteDrop \<and> StructEquiv"

theorem testerr:
shows "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"
by (meson leastConguence name_equivalence)

(*Gives the set of free names in a process*)
primrec free :: "P \<Rightarrow> n set" where
  "free \<^bold>0 = {}"
  | "free (x \<leftarrow> y . P) = {x} \<union> (free(P) - {y})"
  | "free (x \<triangleleft> P \<triangleright>) = {x} \<union> free P"
  | "free (P \<parallel> Q) = free P \<union> free Q"
  | "free (\<acute>x`) = {x}"

value "free (zero \<leftarrow> zero.\<^bold>0)"
value "free (\<^bold>0\<parallel>\<^bold>0)"
value "free (\<acute>zero`)"
value "free (zero\<triangleleft>\<^bold>0\<triangleright>)"

(*
abbreviation Max :: "nat set \<Rightarrow> nat"
  where "Max A \<equiv> fold1 max"
*)
(*quote depth*)


function n_depth :: "n \<Rightarrow> nat"
  and P_depth :: "P \<Rightarrow> nat"
  where
  "n_depth `P\<acute> = (1::nat) + (P_depth P)"
  | "P_depth P = (if (free P \<noteq> {}) then Max({ ( n_depth x ) | x. x \<in> free P}) else 0::nat)"  
  apply pat_completeness
  apply blast
  apply simp
  by blast
termination
sorry

value "P_depth (\<acute>zero`)"

function newName :: "nat \<Rightarrow> n"
  where "newName 0 = `\<^bold>0\<acute>"
       |"newName (Suc n) = `(sugger (newName n) (newName n))\<acute>"
using not0_implies_Suc apply blast
apply simp
apply simp
by blast
termination
using "termination" by blast

value "newName 3"

(*substitution*)
(*Takes a process, specifies the names to be substituted and returns a process*)
abbreviation sn :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n" where
  "sn x q p \<equiv> (if (x =N p) then q else x)" 

  
primrec s :: "P \<Rightarrow> n \<Rightarrow> n \<Rightarrow> P" ("(_) {_\<setminus>_}" 52)
where "(\<^bold>0){_\<setminus>_}             = \<^bold>0"
   | "(R \<parallel> S){q\<setminus>p}          = ((R){q\<setminus>p}) \<parallel> ((S){q\<setminus>p})" 
   | "( x \<leftarrow> y . R){q\<setminus>p}    = R" 
   | "( x\<triangleleft>R\<triangleright>) {q\<setminus>p}         = R"
   | "(\<acute>x`){q\<setminus>p}            = (\<acute>x`)"

end