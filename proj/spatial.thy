theory spatial
imports Main "~~/src/HOL/Library/Multiset"
begin

(*The mutually recursive datatypes of processes and names*)
datatype P = Null             ("\<^bold>0")
           | Input n n P      ("_\<leftarrow>_._" 80)
           | Lift n P         ("_\<triangleleft>_\<triangleright>" 80)
           | Drop n           ("\<acute>_`" 80)
           | Par P P          (infixl "\<parallel>" 75)    
     and n = Quote P          ("`_\<acute>")
termination
  apply size_change
  proof - qed

(*Syntactic sugar for output on a channel*)
abbreviation Output :: "n \<Rightarrow> n \<Rightarrow> P" ("_[_]")
  where "Output x y \<equiv> x\<triangleleft>\<acute>y`\<triangleright>"

abbreviation zero :: n
  where "zero \<equiv> `\<^bold>0\<acute>"


abbreviation reflexiveR
  where "reflexiveR \<equiv> \<lambda> R. \<forall> r. R r r"
abbreviation transitiveR
  where "transitiveR \<equiv> \<lambda> R. \<forall> x. \<forall> y. \<forall> z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation symmetricR
  where "symmetricR \<equiv> \<lambda> R. \<forall> x. \<forall> y. R x y \<longrightarrow> R y x"


value "zero \<leftarrow> zero.\<^bold>0"
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"

fun getSet :: "P \<Rightarrow> P multiset" ("•" 56)
where
  "getSet \<^bold>0 = {#}"
 |"getSet (a\<parallel>b) = (getSet a)+(getSet b)"
 |"getSet a = {#a#}"

  
fun congru :: "P \<Rightarrow> P \<Rightarrow> bool" (infixl "=C" 42)
where
   "congru (a\<parallel>b) (c\<parallel>d) = ((getSet (a\<parallel>b)) = (getSet (c\<parallel>d)))"
  |"congru (a\<parallel>b) c     = ((a =C \<^bold>0 \<and> b =C c) \<or> (b = \<^bold>0 \<and> a =C c))" 
  |"congru  a    (b\<parallel>c) = (( b =C \<^bold>0 \<and> a =C c) \<or> (c =C \<^bold>0 \<and> a =C c))"
  |"congru a b         = (a = b)"




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

*)


value "Null = Null"


theorem congruTransitive:
  shows "transitiveR congru"
sledgehammer
by simp

theorem congruReflexive:
  shows "reflexiveR congru"
by simp

theorem congruSymmetric:
  shows "symmetricR congru"
by simp

theorem someshit:
shows "(((zero\<leftarrow>zero.\<^bold>0) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) =C (((zero\<leftarrow>zero.\<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) \<parallel> \<^bold>0)"
using leastConguence by blast


value "((a \<parallel> b) \<parallel> c) =C (a \<parallel> (b \<parallel> c))"
value "(a \<parallel> (b \<parallel> c)) =C ((a \<parallel> b) \<parallel> c)"
value "(((zero\<leftarrow>zero.\<^bold>0) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) =C (((zero\<leftarrow>zero.\<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) \<parallel> \<^bold>0)"
value "(((zero\<leftarrow>zero.\<^bold>0) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) =C (((zero\<leftarrow>zero.\<^bold>0) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0))"
value "((\<^bold>0 \<parallel> p) \<parallel> \<^bold>0) =C p"

(*
normalization "(Null \<parallel> Null) =C Null"
value[nbe] "(Null\<parallel> Null) =C (Null \<parallel> Null)"

*)


theorem test:
  shows "(p \<parallel> \<^bold>0) =C p"
using leastConguence by blast

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

(*Name equivalence*)
function name_equivalence :: "n \<Rightarrow> n \<Rightarrow> bool" (infix "=N" 52)
  where "`\<acute>x`\<acute> =N y = (x = y)"
  | "zero =N `y\<acute> = (Null =C y)"
  | "((` (Input x y P) \<acute>) =N `z\<acute>) = ((Input x y P)  =C z)"
  | "((` P \<parallel> Q \<acute>) =N `z\<acute>) = ( P \<parallel> Q  =C z)"
  | "((` x\<triangleleft>P\<triangleright> \<acute>) =N `z\<acute>) = (x\<triangleleft>P \<triangleright> =C z)"
  apply pat_completeness
by auto
termination
  by lexicographic_order

abbreviation reflexiveR
  where "reflexiveR \<equiv> \<lambda> R. \<forall> r. R r r"
abbreviation transitiveR
  where "transitiveR \<equiv> \<lambda> R. \<forall> x. \<forall> y. \<forall> z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation symmetricR
  where "symmetricR \<equiv> \<lambda> R. \<forall> x. \<forall> y. R x y \<longrightarrow> R y x"

theorem name_equivalence_reflexive:
  shows "reflexiveR name_equivalence"
sorry 
theorem name_equivalence_symmetric:
  shows "symmetricR name_equivalence"
sorry

theorem name_equivalence_transitive:
  shows "transitiveR name_equivalence"
sorry

value "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"

theorem testerr:
  shows "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"
sorry

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

abbreviation one :: P
  where "one \<equiv> \<acute>newName 1`"
abbreviation two :: P
  where "two \<equiv> \<acute>newName 2`"
abbreviation three :: P
  where "three \<equiv> \<acute>newName 3`"
abbreviation fore :: P
  where "fore \<equiv> \<acute>newName 4`"

value "((one\<parallel>two)\<parallel>(three\<parallel>fore)) =C ((one\<parallel>three)\<parallel>(two\<parallel>fore))"

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
   | "( x\<triangleleft>R\<triangleright>) {q\<setminus>p}         = (sn x q p) \<triangleleft>R{q\<setminus>p}\<triangleright>"
   | "(\<acute>x`){q\<setminus>p}            = (if (x =N p) then \<acute>q` else \<acute>x`)"
apply pat_completeness by auto
termination
  sorry (*induction measure on n_depth*)

value "\<^bold>0{zero\<setminus>zero}"
value "\<acute>zero` {two\<setminus> zero}"
value "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero }"

theorem testerrr:
shows "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero } = (\<^bold>0 \<parallel> (\<acute>(newName 2)`))"
by (simp add: leastConguence name_equivalence)

end