theory spatial
imports Main
begin

abbreviation reflexive
  where "reflexive \<equiv> \<lambda> R. \<forall> r. R r r"
abbreviation transitive
  where "transitive \<equiv> \<lambda> R. \<forall> x. \<forall> y. \<forall> z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation symmetric
  where "symmetric \<equiv> \<lambda> R. \<forall> x. \<forall> y. R x y \<longrightarrow> R y x"


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
abbreviation Output :: "n \<Rightarrow> n \<Rightarrow> P" ("_[[_]]")
  where "Output x y \<equiv> x\<triangleleft>\<acute>y`\<triangleright>"

value "a[[b]]"


abbreviation zero :: n
  where "zero \<equiv> `\<^bold>0\<acute>"


value "zero \<leftarrow> zero.\<^bold>0"
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"
value "(c\<leftarrow>d.(e))"

fun getList :: "P \<Rightarrow> P list"
where
  "getList \<^bold>0 = []"
 |"getList (a\<parallel>b) = ((getList a)@(getList b))"
 |"getList a = [a]"

(*
fun la :: "P \<Rightarrow> P"
where
  "la (a\<parallel>(b\<parallel>c)) = ((la (a\<parallel>b))\<parallel>(la c))"
 |"la a = a"

value "la (Null \<parallel> (Null \<parallel> (Null \<parallel> (Null \<parallel> Null))))"
value "la ((Null \<parallel> Null) \<parallel> (Null \<parallel> (Null \<parallel> Null)))"
*)

function congru :: "P \<Rightarrow> P \<Rightarrow> bool" (infixl "=C" 42)
     and eq2 :: "P list \<Rightarrow> P list \<Rightarrow> P list \<Rightarrow> bool"
     and eq :: "P list \<Rightarrow> P list \<Rightarrow> bool"
where
   "congru (a\<parallel>b) (c\<parallel>d)       = (eq (getList (a\<parallel>b)) (getList (c\<parallel>d)))"
  |"congru (x\<leftarrow>y.(a)) (xx\<leftarrow>yy.(b)) = ((a =C b) \<and> (x=xx) \<and> (y = yy))"
  |"congru (x\<triangleleft>a\<triangleright>) (y\<triangleleft>b\<triangleright>)     = ((a =C b) \<and> (x = y))"
  |"congru (\<acute>a`) (\<acute>b`)       = (a = b)"
  |"congru Null Null         = True"
  |"congru (a\<parallel>b) Null        = ((a =C Null)\<and>(b =C Null))"
  |"congru Null (a\<parallel>b)        = ((a =C Null)\<and>(b =C Null))"
  |"congru (a\<parallel>b) (c\<leftarrow>d.(e))  = (eq (getList (a\<parallel>b)) ((c\<leftarrow>d.(e))#[]))"
  |"congru (c\<leftarrow>d.(e)) (a\<parallel>b)  = (eq (getList (a\<parallel>b)) ((c\<leftarrow>d.(e))#[]))"
  |"congru (a\<parallel>b) (c\<triangleleft>d\<triangleright>)      = (eq (getList (a\<parallel>b)) ((c\<triangleleft>d\<triangleright>)#[]))"
  |"congru (c\<triangleleft>d\<triangleright>) (a\<parallel>b)      = (eq (getList (a\<parallel>b)) ((c\<triangleleft>d\<triangleright>)#[]))"
  |"congru (a\<parallel>b) (\<acute>c`)       = (eq (getList (a\<parallel>b)) ((\<acute>c`)#[]))"
  |"congru (\<acute>c`) (a\<parallel>b)       = (eq (getList (a\<parallel>b)) ((\<acute>c`)#[]))"

  (* for f*cks sake, why cant I have some statement for remaining cases? *)
  |"congru (\<acute>a`) Null        = False"
  |"congru Null (\<acute>b`)        = False"
  |"congru (\<acute>a`) (_\<leftarrow>_._)    = False"
  |"congru (_\<leftarrow>_._) (\<acute>b`)    = False"
  |"congru (\<acute>a`) (_\<triangleleft>_\<triangleright>)      = False"
  |"congru (_\<triangleleft>_\<triangleright>) (\<acute>b`)      = False"
  |"congru (_\<triangleleft>_\<triangleright>) Null       = False"
  |"congru Null (_\<triangleleft>_\<triangleright>)       = False"
  |"congru (_\<triangleleft>_\<triangleright>) (_\<leftarrow>_._)   = False"
  |"congru (_\<leftarrow>_._) (_\<triangleleft>_\<triangleright>)   = False"
  |"congru (_\<leftarrow>_._) Null     = False"
  |"congru Null (_\<leftarrow>_._)     = False"

  |"eq2 [] [] [] = True"
  |"eq2 (x#xs) [] [] = False"
  |"eq2 [] [] (a#as) = False"
  |"eq2 (x#xs) [] (b#bs) = False"
  |"eq2 [] (b#bs) _ = False"
  |"eq2 (x#xs) (y#ys) zs = (if (x =C y) then (eq2 xs (zs@ys) []) else (eq2 (x#xs) ys (y#zs)))"

  |"eq a b = eq2 a b []"

sorry
termination
sorry


value "(( \<^bold>0 \<parallel> (n\<^sub>1\<triangleleft>\<^bold>0 \<parallel> \<^bold>0\<triangleright>)) =C (n\<^sub>1\<triangleleft>\<^bold>0\<triangleright>))"

theorem eqTransitive:
  shows "transitive eq"
sorry

theorem eqReflexive:
  shows "reflexive eq"
sorry

theorem eqSymmetric:
  shows "symmetric eq"
sorry

theorem congruTransitive:
  shows "transitive congru"
sorry

theorem congruReflexive:
  shows "reflexive congru"
sorry

theorem congruSymmetric:
  shows "symmetric congru"
sorry

theorem parAssoc:
  shows "((a\<parallel>b)\<parallel>c) =C (a\<parallel>(b\<parallel>c))"
by (metis append_assoc congru.simps(1) congruReflexive getList.simps(2))

lemma eq_congruence: "eq a a"
sorry

theorem zeroLeft:
  shows "(Null \<parallel> a) =C a"
(*
by (smt congru.simps(1) congru.simps(10) congru.simps(13) congru.simps(5) congru.simps(6) congru.simps(9) congruReflexive congruSymmetric getList.elims getList.simps(1) getList.simps(2) self_append_conv2)
*)
sorry

theorem zeroRight:
  shows "(a \<parallel> Null) =C a"

(*
by (smt append_self_conv congru.simps(1) congru.simps(10) congru.simps(13) congru.simps(5) congru.simps(6) congru.simps(9) congruReflexive congruSymmetric getList.elims getList.simps(1) getList.simps(2))
*)
sorry
theorem yeroright:
  shows "a =C Null \<parallel> a"
by (simp add: congruSymmetric zeroLeft)


theorem someshit:
shows "(((zero\<leftarrow>zero.\<^bold>0) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) =C (((zero\<leftarrow>zero.\<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) \<parallel> \<^bold>0)"
by simp

value "getList ((a \<parallel> b) \<parallel> c)"
value "(((zero\<leftarrow>zero.\<^bold>0) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) =C (((zero\<leftarrow>zero.\<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0)) \<parallel> \<^bold>0)"


(*Name equivalence*)
fun name_equivalence :: "n \<Rightarrow> n \<Rightarrow> bool" (infix "=N" 52)
  where 
    "`\<acute>x`\<acute> =N y = (x =N y)"
  | "x =N `\<acute>y`\<acute> = (x =N y)"
  | "zero =N `y\<acute> = (Null =C y)"
  | "`y\<acute> =N zero = (Null =C y)"
  | "((` (Input x y P) \<acute>) =N `z\<acute>) = ((Input x y P)  =C z)"
  | "(`z\<acute> =N (` (Input x y P) \<acute>)) = ((Input x y P)  =C z)"
  | "((` P \<parallel> Q \<acute>) =N `z\<acute>) = ( P \<parallel> Q  =C z)"
  | "( `z\<acute> =N(` P \<parallel> Q \<acute>)) = ( P \<parallel> Q  =C z)"
  | "((` x\<triangleleft>P\<triangleright> \<acute>) =N `z\<acute>) = (x\<triangleleft>P \<triangleright> =C z)"
(*  | "( `z\<acute> =N (` x\<triangleleft>P\<triangleright> \<acute>)) = (x\<triangleleft>P \<triangleright> =C z)"*)


value "`\<acute>zero`\<acute> =N zero"
value "`\<acute>`\<acute>zero`\<acute>`\<acute> =N zero"

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

value "three"
value "newName 3"
value "`three\<acute>"
value "newName 3 =N (`three\<acute>)"
value "newName 3 =N zero"
value "(`three\<acute>) =N newName 3"


value "`((one\<parallel>two)\<parallel>(three\<parallel>fore))\<parallel>Null\<acute> =N `((one\<parallel>three)\<parallel>(two\<parallel>fore))\<acute>"

(*substitution*)
(*Takes a process, specifies the names to be substituted and returns a process*)
abbreviation sn :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n" where
  "sn x q p \<equiv> (if (x =N p) then q else x)" 

value "(sn zero zero zero)"
value "newName (Max ({(n_depth zero), 0::nat}))"

(*with z = (newName (P_depth(R)))*)
abbreviation genz
  where "genz \<equiv> \<lambda> q::n.  \<lambda> p::n. \<lambda> R::P. newName (Max({(n_depth(q)), (P_depth(R)), (n_depth(p)) }))"
  

function s :: "P \<Rightarrow> n \<Rightarrow> n \<Rightarrow> P" ("(_) {_\<setminus>_}" 52)
where "(\<^bold>0){_\<setminus>_}             = \<^bold>0"
   | "(R \<parallel> S){q\<setminus>p}          = ((R){q\<setminus>p}) \<parallel> ((S){q\<setminus>p})" 
   | "( x \<leftarrow> y . R){q\<setminus>p}    = ((sn x q p) \<leftarrow> (genz q p R)  . ((R {(genz q p R)\<setminus>y}){q\<setminus>p}))"  
   | "(x \<triangleleft> R \<triangleright>) {q\<setminus>p}       = ((sn x q p) \<triangleleft>R{q\<setminus>p}\<triangleright>)"
   | "(\<acute>x`){q\<setminus>p}            = (if (x =N p) then \<acute>q` else \<acute>x`)"
apply pat_completeness by auto
termination
  sorry (*induction measure on n_depth*)

value "\<^bold>0{zero\<setminus>zero}"
value "\<acute>zero` {`two\<acute>\<setminus> zero}"
value "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero }"

(*
 2.6 Dynamic quote: an example
*)

value "zero\<triangleleft>zero[[`three\<acute>]]\<triangleright>{`two\<acute>\<setminus>`three\<acute>}"
value "(zero\<triangleleft>zero[[`three\<acute>]]\<triangleright>{`two\<acute>\<setminus>`three\<acute>}) = (zero\<triangleleft>zero[[`two\<acute>]]\<triangleright>)"

value "zero[[`zero[[`three\<acute>]]\<acute>]]{`two\<acute>\<setminus>`three\<acute>}"
value "zero[[`zero[[`three\<acute>]]\<acute>]]{`two\<acute>\<setminus>`three\<acute>} = (zero[[`zero[[`three\<acute>]]\<acute>]])"

(*
lemma "(zero\<triangleleft>zero[[`three\<acute>]]\<triangleright>{`two\<acute>\<setminus>`three\<acute>}) = (zero\<triangleleft>zero[[`two\<acute>]]\<triangleright>)"
apply simp
apply auto
apply (simp add: numeral_3_eq_3)
proof -
  have 1:"\<not>(zero =N newName 3)" by (simp add: numeral_3_eq_3)
  moreover have 2: "newName 3 =N `three\<acute>" by (simp add: numeral_3_eq_3)
  moreover have 3: "\<not> newName 2 = newName 3" by (simp add: numeral_3_eq_3 numeral_2_eq_2)

how to prove this?
*)




theorem testerrr:
shows "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero } = (\<^bold>0 \<parallel> (\<acute>(newName 2)`))"
by simp

(*theory is consistent, yay*)
lemma False
sledgehammer
oops

end