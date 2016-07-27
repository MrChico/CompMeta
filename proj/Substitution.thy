theory Substitution
imports RhoCalc NameEquiv 
begin

section\<open>Substitution\<close>
text\<open>In the rho-calculus, we deal with two different notions of substitution, a syntactical and a
semantic one, differing in the way which we deal with dropped names. One can think of the 
semantic substitution as a way of making sure that the process about to be run will be executed
in the correct context.\<close> 
subsection\<open>Free and bound names\<close>
(*Gives the set of free names in a process*)
fun free :: "P \<Rightarrow> n set" where
  "free \<^bold>0 = {}"
  | "free (x \<leftarrow> y . P.) = {x} \<union> (free(P) - {y})"
  | "free (x \<triangleleft> P \<triangleright>) = {x} \<union> free P"
  | "free (P \<parallel> Q) = free P \<union> free Q"
  | "free (\<acute>x`) = {x}"

(*Gives the set of bound names in a process*)
fun bound :: "P \<Rightarrow> n set" where
  "bound \<^bold>0 = {}"
  | "bound (x \<leftarrow> y . P.) = {y} \<union> bound(P)"
  | "bound (x \<triangleleft> P \<triangleright>) = bound P"
  | "bound (P \<parallel> Q) = bound P \<union> bound Q"
  | "bound (\<acute>x`) = {}"

(*Total set of names occurring in a process*)
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


subsection\<open>Syntactic substitution\<close>
text\<open>The base case is a substitution of names if they are name equivalent:
\<close>
abbreviation sn :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n" where
  "sn x q p \<equiv> (if (x =N p) then q else x)" 

value "(sn zero zero zero)"
value "newName (Max ({(n_depth zero), 0::nat}))"

text\<open>Generate new name not used in the relevant processes\<close>
abbreviation genz
  where "genz \<equiv> \<lambda> q::n.  \<lambda> p::n. \<lambda> R::P. newName (Max({(n_depth(q)), (P_depth(R)), (n_depth(p)) }))"
  
text\<open>Syntactic substitution can now be given by the following function:\<close>
function s :: "P \<Rightarrow> n \<Rightarrow> n \<Rightarrow> P" ("(_) {_\<setminus>_}" 52)
where "(\<^bold>0){_\<setminus>_}             = \<^bold>0"
   | "(R \<parallel> S){q\<setminus>p}          = ((R){q\<setminus>p}) \<parallel> ((S){q\<setminus>p})" 
   | "( x \<leftarrow> y . R.){q\<setminus>p}    = ((sn x q p) \<leftarrow> (genz q p R)  . ((R {(genz q p R)\<setminus>y}){q\<setminus>p}).)"  
   | "(x \<triangleleft> R \<triangleright>) {q\<setminus>p}       = ((sn x q p) \<triangleleft>R{q\<setminus>p}\<triangleright>)"
   | "(\<acute>x`){q\<setminus>p}            = (if (x =N p) then \<acute>q` else \<acute>x`)"
apply pat_completeness by auto
termination
apply (relation "measure (\<lambda>(p,x,y). (P_depth p))", auto)
(* see http://isabelle.in.tum.de/doc/functions.pdf *)
  sorry (*induction measure on n_depth*)
  
subsection\<open>Semantic substitution\<close>
function ss :: "P \<Rightarrow> n \<Rightarrow> n \<Rightarrow> P" ("(_) s{_\<setminus>_}" 52)
where "(\<^bold>0)s{_\<setminus>_}             = \<^bold>0"
   | "(R \<parallel> S) s{q\<setminus>p}          = ((R) s{q\<setminus>p}) \<parallel> ((S) s{q\<setminus>p})" 
   | "( x \<leftarrow> y . R.) s{q\<setminus>p}    = ((sn x q p) \<leftarrow> (genz q p R)  . ((R {(genz q p R)\<setminus>y}) s{q\<setminus>p}).)"  
   | "(x \<triangleleft> R \<triangleright>) s{q\<setminus>p}       = ((sn x q p) \<triangleleft>R s{q\<setminus>p}\<triangleright>)"
   | "(\<acute>x`) s{`q\<acute>\<setminus>p}            = (if (x =N p) then q else \<acute>x`)" (* semantic substitution *)
apply pat_completeness by auto
termination
apply (relation "measure (\<lambda>(p,x,y). (P_depth p))", auto)

(* see http://isabelle.in.tum.de/doc/functions.pdf *)
  sorry (*induction measure on n_depth*)


subsection\<open>Examples\<close>
value "\<^bold>0{zero\<setminus>zero}"
value "(zero \<leftarrow> zero . Zero.){two \<setminus> zero}"
value "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero }"

(*
 2.6 Dynamic quote: an example
*)

value "zero\<triangleleft>zero[[three]]\<triangleright>{two\<setminus>three}"
value "(zero\<triangleleft>zero[[three]]\<triangleright>{two\<setminus>three}) = (zero\<triangleleft>zero[[two]]\<triangleright>)"

value "zero[[`zero[[three]]\<acute>]]{two\<setminus>three}"
value "zero[[`zero[[three]]\<acute>]]{two\<setminus>three} = (zero[[`zero[[three]]\<acute>]])"

section\<open>Alpha equivalence\<close>
text\<open>Alpha equivalence equates processes that only differ by their bound variables. In our calculus,
the bound variables are the names to which we bind input values.\<close>

(*Bound variable names do not matter under \<alpha>-equivalence
  WIP*)
function alphaEq :: "P \<Rightarrow> P \<Rightarrow> bool" (infix "\<equiv>\<alpha>" 52)
  and listEq :: "P list \<Rightarrow> P list \<Rightarrow> P list \<Rightarrow> bool"
  where "Null \<equiv>\<alpha> Null = True"
    (*The interesting cases are the ones relating to the bound variable of input*)
    | "((a\<leftarrow>b. P.) \<equiv>\<alpha> (c\<leftarrow>d. Q.)) =  ((b =N d) \<and> (P \<equiv>\<alpha> (Q{a\<setminus>c})))"
    | "(a\<leftarrow>b. P.) \<equiv>\<alpha> Q\<parallel>R = (listEq (getList (Q\<parallel>R)) ((a\<leftarrow>b.(P).)#[]) [])"
    | "Q\<parallel>R \<equiv>\<alpha> (a\<leftarrow>b. P.) = (listEq (getList (Q\<parallel>R)) ((a\<leftarrow>b.(P).)#[]) [])"
    (*What follows is analoguous to the procedure of structural equality*)
    | "P\<parallel>Q \<equiv>\<alpha> R\<parallel>S = (listEq (getList (P\<parallel>Q)) (getList (R\<parallel>S)) [])"
    |"(x\<triangleleft>a\<triangleright>) \<equiv>\<alpha> (y\<triangleleft>b\<triangleright>)     = ((a =C b) \<and> (x =N y))"
    |"(\<acute>a`) \<equiv>\<alpha> (\<acute>b`)       = (a =N b)"
    |"(a\<parallel>b) \<equiv>\<alpha> Null        = ((a =C Null)\<and>(b =C Null))"
    |"Null \<equiv>\<alpha> (a\<parallel>b)        = ((a =C Null)\<and>(b =C Null))"
    |"(a\<parallel>b) \<equiv>\<alpha> (c\<leftarrow>d.(e).)  = (listEq (getList (a\<parallel>b)) ((c\<leftarrow>d.(e).)#[]) [])"
    |"(c\<leftarrow>d.(e).) \<equiv>\<alpha> (a\<parallel>b)  = (listEq (getList (a\<parallel>b)) ((c\<leftarrow>d.(e).)#[]) [])"
    |"(a\<parallel>b) \<equiv>\<alpha> (c\<triangleleft>d\<triangleright>)      = (listEq (getList (a\<parallel>b)) ((c\<triangleleft>d\<triangleright>)#[]) [])"
    |"(c\<triangleleft>d\<triangleright>) \<equiv>\<alpha> (a\<parallel>b)      = (listEq (getList (a\<parallel>b)) ((c\<triangleleft>d\<triangleright>)#[]) [])"
    |"(a\<parallel>b) \<equiv>\<alpha> (\<acute>c`)       = (listEq (getList (a\<parallel>b)) ((\<acute>c`)#[]) [])"
    |"(\<acute>c`) \<equiv>\<alpha> (a\<parallel>b)       = (listEq (getList (a\<parallel>b)) ((\<acute>c`)#[]) [])"
    (*Uninteresting remaining cases*)
    |"(\<acute>a`) \<equiv>\<alpha> Null        = False"
    |"Null \<equiv>\<alpha> (\<acute>b`)        = False"
    |"(\<acute>a`) \<equiv>\<alpha> (_\<leftarrow>_._.)    = False"
    |"(_\<leftarrow>_._.) \<equiv>\<alpha> (\<acute>b`)    = False"
    |"(\<acute>a`)\<equiv>\<alpha> (_\<triangleleft>_\<triangleright>)      = False"
    |"(_\<triangleleft>_\<triangleright>)\<equiv>\<alpha> (\<acute>b`)      = False"
    |"(_\<triangleleft>_\<triangleright>)\<equiv>\<alpha> Null       = False"
    |"Null \<equiv>\<alpha>(_\<triangleleft>_\<triangleright>)       = False"
    |"(_\<triangleleft>_\<triangleright>)\<equiv>\<alpha> (_\<leftarrow>_._.)   = False"
    |"(_\<leftarrow>_._.)\<equiv>\<alpha> (_\<triangleleft>_\<triangleright>)   = False"
    |"(_\<leftarrow>_._.)\<equiv>\<alpha> Null     = False"
    |"Null \<equiv>\<alpha> (_\<leftarrow>_._.)     = False"
    
    |"listEq [] [] [] = True"
    |"listEq (x#xs) [] [] = False"
    |"listEq [] [] (a#as) = False"
    |"listEq (x#xs) [] (b#bs) = False"
    |"listEq [] (b#bs) _ = False"
    |"listEq (x#xs) (y#ys) zs = (if (x \<equiv>\<alpha> y) then (eq2 xs (zs@ys) []) else (eq2 (x#xs) ys (y#zs)))"
by (auto, pat_completeness)
termination
sorry
 (*placeholder*) 

text\<open> As an example, the 
following terms are alpha-equal: \<close>
value "(zero \<leftarrow> zero . Zero.) \<equiv>\<alpha> (one \<leftarrow> zero . Zero.)"
value "(Zero \<parallel> (zero \<leftarrow> zero . Zero.)) \<equiv>\<alpha> (one \<leftarrow> zero . Zero. \<parallel> Zero)"
value "(zero \<leftarrow> zero . (zero \<triangleleft> Zero \<triangleright>).) \<equiv>\<alpha> (one \<leftarrow> zero . one \<triangleleft> Zero \<parallel> Zero \<triangleright>.)"

end