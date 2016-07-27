theory spatial
imports Main
begin

declare [[ smt_timeout = 20 ]]

abbreviation reflexive
  where "reflexive \<equiv> \<lambda> R. \<forall> r. R r r"
abbreviation transitive
  where "transitive \<equiv> \<lambda> R. \<forall> x. \<forall> y. \<forall> z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation symmetric
  where "symmetric \<equiv> \<lambda> R. \<forall> x. \<forall> y. R x y \<longrightarrow> R y x"


(*The mutually recursive datatypes of processes and names*)
datatype P = Null             ("\<^bold>0")
           | Input n n P      ("_\<leftarrow>_._." 80)
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
value "zero \<leftarrow> zero.\<^bold>0"
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"
value "(c\<leftarrow>d.(e))"


fun newName :: "nat \<Rightarrow> n"
  where "newName 0 = `\<^bold>0\<acute>"
       |"newName (Suc n) = `(Output (newName n) (newName n))\<acute>"

abbreviation zero :: n
  where "zero \<equiv> `\<^bold>0\<acute>"
abbreviation one :: n
  where "one \<equiv> newName 1"
abbreviation two :: n
  where "two \<equiv> newName 2"
abbreviation three :: n
  where "three \<equiv> newName 3"
abbreviation four :: n
  where "four \<equiv> newName 4"

abbreviation Zero :: P
  where "Zero \<equiv> Null"
abbreviation One :: P
  where "One \<equiv> \<acute>one`"
abbreviation Two :: P
  where "Two \<equiv> \<acute>two`"
abbreviation Three :: P
  where "Three \<equiv> \<acute>three`"
abbreviation Four :: P
  where "Four \<equiv> \<acute>four`" 

value "zero \<leftarrow> zero.\<^bold>0."
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"
value "(c\<leftarrow>d.(e).)"

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
where
   "congru (a\<parallel>b) (c\<parallel>d)       = (eq2 (getList (a\<parallel>b)) (getList (c\<parallel>d)) [])"
  |"congru (x\<leftarrow>y.(a).) (xx\<leftarrow>yy.(b).) = ((a =C b) \<and> (x=xx) \<and> (y = yy))"
  |"congru (x\<triangleleft>a\<triangleright>) (y\<triangleleft>b\<triangleright>)     = ((a =C b) \<and> (x = y))"
  |"congru (\<acute>a`) (\<acute>b`)       = (a = b)"
  |"congru Null Null         = True"
  |"congru (a\<parallel>b) Null        = ((a =C Null)\<and>(b =C Null))"
  |"congru Null (a\<parallel>b)        = ((a =C Null)\<and>(b =C Null))"
  |"congru (a\<parallel>b) (c\<leftarrow>d.(e).)  = (eq2 (getList (a\<parallel>b)) ((c\<leftarrow>d.(e).)#[]) [])"
  |"congru (c\<leftarrow>d.(e).) (a\<parallel>b)  = (eq2 (getList (a\<parallel>b)) ((c\<leftarrow>d.(e).)#[]) [])"
  |"congru (a\<parallel>b) (c\<triangleleft>d\<triangleright>)      = (eq2 (getList (a\<parallel>b)) ((c\<triangleleft>d\<triangleright>)#[]) [])"
  |"congru (c\<triangleleft>d\<triangleright>) (a\<parallel>b)      = (eq2 (getList (a\<parallel>b)) ((c\<triangleleft>d\<triangleright>)#[]) [])"
  |"congru (a\<parallel>b) (\<acute>c`)       = (eq2 (getList (a\<parallel>b)) ((\<acute>c`)#[]) [])"
  |"congru (\<acute>c`) (a\<parallel>b)       = (eq2 (getList (a\<parallel>b)) ((\<acute>c`)#[]) [])"

  (* for f*cks sake, why cant I have some statement for remaining cases? *)
  |"congru (\<acute>a`) Null        = False"
  |"congru Null (\<acute>b`)        = False"
  |"congru (\<acute>a`) (_\<leftarrow>_._.)    = False"
  |"congru (_\<leftarrow>_._.) (\<acute>b`)    = False"
  |"congru (\<acute>a`) (_\<triangleleft>_\<triangleright>)      = False"
  |"congru (_\<triangleleft>_\<triangleright>) (\<acute>b`)      = False"
  |"congru (_\<triangleleft>_\<triangleright>) Null       = False"
  |"congru Null (_\<triangleleft>_\<triangleright>)       = False"
  |"congru (_\<triangleleft>_\<triangleright>) (_\<leftarrow>_._.)   = False"
  |"congru (_\<leftarrow>_._.) (_\<triangleleft>_\<triangleright>)   = False"
  |"congru (_\<leftarrow>_._.) Null     = False"
  |"congru Null (_\<leftarrow>_._.)     = False"

  |"eq2 [] [] [] = True"
  |"eq2 (x#xs) [] [] = False"
  |"eq2 [] [] (a#as) = False"
  |"eq2 (x#xs) [] (b#bs) = False"
  |"eq2 [] (b#bs) _ = False"
  |"eq2 (x#xs) (y#ys) zs = (if (x =C y) then (eq2 xs (zs@ys) []) else (eq2 (x#xs) ys (y#zs)))"
by (auto, pat_completeness)

(* 
  in order to proof the termination I'd need to find a measure function
  the bad part is that i need to prove the termination of this counting function as well
 *)

abbreviation maxl where "maxl \<equiv> \<lambda>l. foldl (\<lambda>a.\<lambda>b. (max a b)) 0 l"

fun sdepth :: "P \<Rightarrow> nat" where
  "sdepth Null = 0"
  | "sdepth (x \<leftarrow> y . P.) = 1 + sdepth P"
  | "sdepth (x \<triangleleft> P \<triangleright>) = 1 + sdepth P"
  | "sdepth (P \<parallel> Q) = 1 + (max (sdepth P) (sdepth Q))"
  | "sdepth (\<acute>x`) = 0"

fun di::"nat \<Rightarrow> nat" where 
  "di 0 = 0"
| "di (Suc(Suc v)) = (Suc (di v))"


abbreviation llength where "llength \<equiv> \<lambda>x::P list. (di ((length x)*(length x + 1)))"


function
  depth :: "P \<Rightarrow> nat"
where
  "depth \<^bold>0 = 0"
  | "depth (x \<leftarrow> y . P.) = 1 + depth P"
  | "depth (x \<triangleleft> P \<triangleright>) = 1 + depth P"
  | "depth (P \<parallel> Q) = 1 + (maxl (map depth (getList (P\<parallel>Q)))) + llength (getList (P\<parallel>Q))"
  | "depth (\<acute>x`) = 0"
apply auto
apply pat_completeness
done
termination
apply (relation "measure (\<lambda>x.(sdepth x))")
apply auto
(*proof -
  fix P Q x
  assume "x\<in> set (getList P)"
  show "sdepth x < Suc (max (sdepth P) (sdepth Q))"
  (* damn it, so close *)*)
sorry

termination congru
(* cannot come up with a good measuring function without *)
apply (relation "measure (
\<lambda>x. case x of 
  Inl (a,b) 
    \<Rightarrow> (Max({depth a, depth b})) 
| Inr (a,b,c) 
    \<Rightarrow> max (maxl (map depth (a))) (maxl (map depth (b@c))) )")
apply auto
sorry


value "(( \<^bold>0 \<parallel> (n\<^sub>1\<triangleleft>\<^bold>0 \<parallel> \<^bold>0\<triangleright>)) =C (n\<^sub>1\<triangleleft>\<^bold>0\<triangleright>))"



(*
theorem eqReflexive:
  assumes "reflexive congru"
  shows "reflexive eq"
proof 
  fix r
  show "eq r r"
  proof (induction r)
    show "eq [] []" by simp
  next
    fix a r
    assume eqr: "eq r r"
    show "eq (a#r) (a#r)"
    proof auto
      assume "a =C a"
      show "eq2 r r []" using eqr by auto
    next
      assume na: "\<not> a =C a"
      show "eq2 (a#r) r [a]"
      proof -
       (* assume req: "reflexive eq"
        from this req have "reflexive congru" by (meson assms eq.elims(2) eq2.simps(4) eq2.simps(6))*)
        from assms have "a =C a" by simp
        from this na show "eq2 (a#r) r [a]" by simp (* i want to prove this through contradiction *)
      qed
    qed
  qed  
qed

lemma "getList r = getList r" by simp
*)

(*
lemma listtocongru:
  assumes "eq2 (getList a) (getList a) []"
  shows "a =C a"
  apply (induction a)
  apply auto
  proof -
    fix a1 a2
    assume "a1 =C a1" and "a2 =C a2"
    show "eq2 (getList a1 @ getList a2) (getList a1 @ getList a2) []"
    apply (induction a1)
    apply auto    
sorry
*)

(*
lemma congrutolist:
  assumes "a =C a"
  shows "eq2 (getList a) (getList a) []"
  apply (induction a)
  apply auto
  apply (simp add: listtocongru)
  apply (simp add: listtocongru) 
  proof -
    fix a1 a2
    assume h1: "eq2 (getList a1) (getList a1) []"
    assume h2: "eq2 (getList a2) (getList a2) []"
    show "eq2 (getList a1 @ getList a2) (getList a1 @ getList a2) []"
    apply (induction a1)
    apply auto
    apply (simp add: h1 h2)
    apply (simp add: h1 h2)
    proof (rule ccontr)
      fix x1 x2a a1
      assume "eq2 (getList a1 @ getList a2) (getList a1 @ getList a2) []"
      assume "\<not> a1 =C a1"
      from assms have "a1 =C a1"

sorry

lemma partolist:
  assumes "a =C a" and "b =C b"
  shows "eq2 ((getList a)@(getList b)) ((getList a)@(getList b)) []"
sorry
*)
(*
  proof (auto, induction r1)
      show "eq2 (getList \<^bold>0 @ getList r2) (getList \<^bold>0 @ getList r2) []"
      apply auto
      apply (simp add: congrutolist b)
      done
    next
      fix x1 x2a::n
      fix P2:: "n \<Rightarrow> bool"
      assume "P2 x1"
      assume "P2 x2a"
      assume "eq2 (getList r1 @ getList r2) (getList r1 @ getList r2) []" 
      show "eq2 (getList (x1\<leftarrow>x2a.(r1)) @ getList r2) (getList (x1\<leftarrow>x2a.(r1)) @ getList r2) []"
      proof -
*)


(*
theorem asdadsds:
  assumes "\<forall> a. a =C a"
  shows "eq (getList a) (getList a)"
  apply auto
  apply (induction a)
  apply auto
  apply (simp add: listtocongru)
  apply (simp add: listtocongru) 
  proof -
    fix a1 a2
    assume h1: "eq2 (getList a1) (getList a1) []"
    assume h2: "eq2 (getList a2) (getList a2) []"
    show "eq2 (getList a1 @ getList a2) (getList a1 @ getList a2) []"
    apply (induction a1)
    apply auto
    apply (simp add: h1 h2)
    apply (simp add: h1 h2)
    proof (rule ccontr)
      fix x1 x2a a1
      assume "eq2 (getList a1 @ getList a2) (getList a1 @ getList a2) []"
      assume "\<not> a1 =C a1"
      from assms have "a1 =C a1"
    sledgehammer
*)
(*
theorem congruReflexive:
  shows "reflexive congru"
  and "\<forall>b::P. eq2 (getList b) (getList b) []"
proof auto
  fix r
  fix b::P
  show "r =C r"  "eq2 (getList r) (getList r) []"
  apply (induct r)
  apply auto
  proof -
    show "Null =C Null" by simp
  next
    fix x1 x2a r2
    assume "r2 =C r2"
    show "(Input x1 x2a r2 =C Input x1 x2a r2)" by (simp add: \<open>r2 =C r2\<close>)
  next
    fix x1 r2
    assume a:"r2 =C r2"
    show "(x1\<triangleleft>r2\<triangleright>) =C (x1\<triangleleft>r2\<triangleright>)" by (simp add: a)
  next
    fix x
    show "\<acute>x` =C \<acute>x`" by simp
  next
    fix r1 r2
    assume a: "r1 =C r1" and b: "r2 =C r2"
    show "(r1\<parallel>r2) =C (r1\<parallel>r2)"
    apply auto
    apply (simp add: a b partolist)
    done
  next
    (* I have no idea what I have to show here!? *)
    fix r2
    fix P2::"n \<Rightarrow> bool"
    assume "r2 =C r2"
    show "P2 `r2\<acute>"
    sorry
  next
  qed
qed
*)


theorem congruReflexive:
  shows "reflexive congru"
sorry

theorem congruTransitive:
  shows "transitive congru"
sorry

theorem congruSymmetric:
  shows "symmetric congru"
sorry

theorem eqReflexive:
  shows "\<forall> a b. (eq2 a a [])"
sorry

theorem eqSymmetric:
  shows "\<forall> a b. (eq2 a b [] \<longrightarrow> eq2 b a [])"
sorry

theorem eqTransitive:
  shows "\<forall> a b c. (((eq2 a b []) \<and> (eq2 b c [])) \<longrightarrow> (eq2 a c []))"
sorry

theorem parAssoc:
  shows "((a\<parallel>b)\<parallel>c) =C (a\<parallel>(b\<parallel>c))"
sorry

theorem parKommutative:
  shows "a\<parallel>b =C b\<parallel>a"
sorry

theorem zeroLeft:
  shows "(Null \<parallel> a) =C a"
sorry

theorem zeroRight:
  shows "(a \<parallel> Null) =C a"
sorry

theorem someshit:
shows "(((zero\<leftarrow>zero.\<^bold>0.) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) =C (((zero\<leftarrow>zero.\<^bold>0.) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) \<parallel> \<^bold>0)"
by simp

value "getList ((a \<parallel> b) \<parallel> c)"
value "(((zero\<leftarrow>zero.\<^bold>0.) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) =C (((zero\<leftarrow>zero.\<^bold>0.) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) \<parallel> \<^bold>0)"


(*Name equivalence*)
fun name_equivalence :: "n \<Rightarrow> n \<Rightarrow> bool" (infix "=N" 52)
  where 
    "zero =N `Input x y P\<acute> = False"
  | "zero =N `Lift _ _\<acute> = False"
  | "zero =N `Par P Q\<acute> = (Null =C (P\<parallel>Q))"
  | "zero =N `\<acute>a`\<acute> = (zero =N a)"
  | "zero =N zero = True"

  | "((`(Input x y P)\<acute>) =N `Input p q Q\<acute>) = ((Input x y P)  =C (Input p q Q))"
  | "((`(Input x y P)\<acute>) =N `Lift _ _\<acute>) = False"
  | "((`(Input x y P)\<acute>) =N `Par _ _\<acute>) = False"
  | "((`(Input x y P)\<acute>) =N zero) = False"
  | "((`(Input x y P)\<acute>) =N `\<acute>a`\<acute>) = (`(Input x y P)\<acute> =N a)"

  | "((`Lift x P\<acute>) =N `Lift y Q\<acute>) = (Lift x P =C Lift y Q)"
  | "((`Lift x P\<acute>) =N `Input _ _ _\<acute>) = False"
  | "((`Lift x P\<acute>) =N `Par _ _\<acute>) = False"
  | "((`Lift x P\<acute>) =N zero) = False"
  | "((`Lift x P\<acute>) =N `\<acute>a`\<acute>) = (`(Lift x P)\<acute> =N a)"

  | "((`P\<parallel>Q\<acute>) =N (`A\<parallel>B\<acute>)) = ((P\<parallel>Q) =C (A\<parallel>B))"
  | "((`P\<parallel>Q\<acute>) =N (`Lift _ _\<acute>)) = False"
  | "((`P\<parallel>Q\<acute>) =N (`Input _ _ _\<acute>)) = False"
  | "((`P\<parallel>Q\<acute>) =N zero) = ((P\<parallel>Q) =C Null)"
  | "((`P\<parallel>Q\<acute>) =N (`\<acute>a`\<acute>)) = (`(P\<parallel>Q)\<acute> =N a)"

  | "`\<acute>a`\<acute> =N `Input x y P\<acute> = (a =N `Input x y P\<acute>)"
  | "`\<acute>a`\<acute> =N `Lift x P\<acute> = (a =N `Lift x P\<acute>)"
  | "`\<acute>a`\<acute> =N `Par P Q\<acute> = (a =N `Par P Q\<acute>)"
  | "`\<acute>a`\<acute> =N `\<acute>b`\<acute> = (a =N b)"
  | "`\<acute>a`\<acute> =N zero = (a =N zero)"


value "`\<acute>zero`\<acute> =N zero"
value "`\<acute>`\<acute>zero`\<acute>`\<acute> =N zero"
value "newName 3 =N three"
value "newName 3 =N zero"
value "three =N newName 3"
value "`((One\<parallel>Two)\<parallel>(Three\<parallel>Four))\<parallel>Null\<acute> =N `((One\<parallel>Three)\<parallel>(Two\<parallel>Four))\<acute>"

theorem name_equivalence_reflexive:
  shows "reflexive name_equivalence"
apply auto
proof -
  fix r
  show "r =N r"
  using congruReflexive by (induction r rule: name_equivalence.induct, auto)
qed

theorem name_equivalence_symmetric:
  assumes "x =N y"
  shows "y =N x"
using assms congruSymmetric eqSymmetric by (induct x rule: name_equivalence.induct, auto)

theorem name_equivalence_transitive:
  assumes "a =N b" and "b =N c"
  shows "a =N c"
(* I dont know how to make an induction argument here which runs over all three variables *)
(*
using assms apply (induct a c rule: name_equivalence.induct)
apply auto
apply (simp add: assms congruTransitive eqTransitive)
*)
sorry


value "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"

theorem testNameEQ1:
  shows "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"
using parKommutative by auto

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


(*substitution*)
(*Takes a process, specifies the names to be substituted and returns a process*)

abbreviation sn :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n" where
  "sn x q p \<equiv> (if (x =N p) then q else x)" 

value "(sn zero zero zero)"
value "newName (Max ({(n_depth zero), 0::nat}))"

(*with z = (newName (P_depth(R)))*)
abbreviation genz
  where "genz \<equiv> \<lambda> q::n.  \<lambda> p::n. \<lambda> R::P. newName (Max({(n_depth(q)), (P_depth(R)), (n_depth(p)) }))"
  
(* syntactic substitution *)
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
  
(* semantic substitution *)
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

value "\<^bold>0{zero\<setminus>zero}"
value "(zero \<leftarrow> zero . Zero){two \<setminus> zero}"
value "(\<^bold>0 \<parallel> (\<acute>zero`)) { (newName 2) \<setminus> zero }"

(*
 2.6 Dynamic quote: an example
*)

value "zero\<triangleleft>zero[[three]]\<triangleright>{two\<setminus>three}"
value "(zero\<triangleleft>zero[[three]]\<triangleright>{two\<setminus>three}) = (zero\<triangleleft>zero[[two]]\<triangleright>)"

value "zero[[`zero[[three]]\<acute>]]{two\<setminus>three}"
value "zero[[`zero[[three]]\<acute>]]{two\<setminus>three} = (zero[[`zero[[three]]\<acute>]])"

(* Operational Semantics *)

fun toPar:: "P list \<Rightarrow> P" where
  "toPar []   = Null"
 |"toPar (x#[]) = x"
 |"toPar (x#y#xs) = (x \<parallel> (toPar (y#xs)))"



fun syncable:: "P \<Rightarrow> P \<Rightarrow> bool" where
  "syncable (Lift x Q) (Input y z P)    = (x =N z)"
 |"syncable (Input y z P) (Lift x Q)    = (x =N z)"
 |"syncable (Lift y P) (Lift x Q)       = False"
 |"syncable (Input y z P) (Input a b Q) = False"
 |"syncable _ (vc \<parallel> vd)                 = False"
 |"syncable   (vc \<parallel> vd) _               = False"
 |"syncable   (\<acute>v`) _                   = False"
 |"syncable _ (\<acute>v`)                     = False"
 |"syncable   Null _                    = False"
 |"syncable _ Null                      = False"

fun sync:: "P \<Rightarrow> P \<Rightarrow> P" where
  "sync (Lift x Q) (Input y z P) = (P s{`Q\<acute>\<setminus>y})"
 |"sync (Input y z P) (Lift x Q) = (P s{`Q\<acute>\<setminus>y})"

function fineRun:: "P list \<Rightarrow> P list \<Rightarrow> P list \<Rightarrow> P list" where
   "fineRun []     []  []         = []"
  |"fineRun (x#[]) []  []         = (x#[])"
  |"fineRun (x#y#xs) []  zs       = (fineRun (y#xs) (x#[]) zs)"
  |"fineRun [] (y#ys) (z#[])      = (z#y#ys)"
  |"fineRun [] (y#ys) (z#zs)      = (fineRun zs (z#y#ys) [])"
  |"fineRun (x#xs) (y#ys) zs      = (if (syncable x y) then ((sync x y)#xs@ys@zs) else (fineRun (xs) (y#ys) (x#zs)))"
apply auto
sorry
termination
sorry

fun step:: "P \<Rightarrow> P" where
  "step P = toPar( fineRun (getList P) [] [])"


abbreviation replication where "replication \<equiv> (\<lambda>y.\<lambda>(P,x).(x\<triangleleft>((y\<leftarrow>x.(x[[y]]\<parallel>\<acute>y`).)\<parallel>P)\<triangleright>\<parallel>(y \<leftarrow> x.(x[[y]]\<parallel>\<acute>y`).)))(`zero[[zero]]\<acute>)"
abbreviation xx where "xx \<equiv> zero"
abbreviation yy where "yy \<equiv> `xx[[xx]]\<acute>"

value "(replication (two, zero))"
value "step (replication (two, zero))"
value "step(step (replication (two, zero)))"
value "step(step(step (replication (two, zero))))"
value "step(step(step(step (replication (two, zero)))))"


lemma False
sledgehammer
(*theory is consistent, yay*)
oops

section\<open>Alpha equivalence\<close>
text\<open>Alpha equivalence equates processes that only differ by their bound variables. In our calculus,
the bound variables are the names to which we bound input values. As an example we would want the 
following terms to be alpha-equal: \<close>

theorem alphaEq: 
shows "zero \<leftarrow> zero . Zero \<equiv>\<alpha> one \<leftarrow> zero . Zero"
sorry

end