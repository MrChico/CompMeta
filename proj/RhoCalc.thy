theory RhoCalc
imports Main
begin 

section\<open>Introduction\<close>
text\<open>This is a formalization of a reflective, higher order process calculus known as the 
rho-calculus and its associated logic, namespace logic. 
The calculus is described by Greg Meredith in detail in the following resources:\\
\begin{itemize}
\item \href{http://www.lshift.net/downloads/ex_nihilo_logic.pdf}{Namespace Logic}
\item \href{https://arxiv.org/pdf/1307.7766v2.pdf}{Policy as Types}
\end{itemize}
The main differentiating feature of the rho-calculus is that names have structure: they are built
up out of quoted processes. Along with the ability to unquote or "drop" a name back to a process,
this gives the calulus its higher order nature. 
\<close>
(*The mutually recursive datatypes of processes and names*)
datatype P = Null             ("\<^bold>0") 
           | Input n n P      ("_\<leftarrow>_._." 80) (*x \<leftarrow> y. P Listen on y, write to x and then run P*)
           | Lift n P         ("_\<triangleleft>_\<triangleright>" 80) (*Outputs a process within the triangles to the name before it*)
           | Drop n           ("\<acute>_`" 80) (*Unquote/run the process*)
           | Par P P          (infixl "\<parallel>" 75) 
     and n = Quote P          ("`_\<acute>")

(*Syntactic sugar for output on a channel*)
abbreviation Output :: "n \<Rightarrow> n \<Rightarrow> P" ("_[[_]]")
  where "Output x y \<equiv> x\<triangleleft>\<acute>y`\<triangleright>"

abbreviation zero :: n
  where "zero \<equiv> `\<^bold>0\<acute>"

(*Some examples*)
value "a[[b]]"
value "zero \<leftarrow> zero.\<^bold>0."
value "\<^bold>0\<parallel>\<^bold>0"
value "\<acute>zero`"
value "zero\<triangleleft>\<^bold>0\<triangleright>"
value "(c\<leftarrow>d.(e).)"

(*Creating new names by recursion over the output process*)
fun newName :: "nat \<Rightarrow> n"
  where "newName 0 = `\<^bold>0\<acute>"
       |"newName (Suc n) = `(Output (newName n) (newName n))\<acute>"

(*We use begin names with lower case and processes with upper case*) 

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

section\<open>Structural congruence\<close>
text\<open>The smallest congruence we require is structural congruence, which expresses the fact that
parallelisation is commutative and associative, and running a process parallell with the Null
process is the same as running that process on its own. In Meredith's paper, this is captured by
the equations:

\begin{equation}
P | Null \equiv_C P \equiv_C Null | P
\end{equation}
\begin{equation}
P | Q & \equiv_C Q | P
\end{equation}
\begin{equation}
(P | Q) | R \equiv_C P (Q | R)
\end{equation}
While this seems fairly straight forward, trying to formalise this notion turns out to be quite
verbose. In order to do this, we create a list of processes running in parallel and then create
the structural congruence relation as a mutually recursive function comparing lists and "atomic"
processes.
\<close>
fun getList :: "P \<Rightarrow> P list"
where
  "getList \<^bold>0 = []"
 |"getList (a\<parallel>b) = ((getList a)@(getList b))"
 |"getList a = [a]"


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

  (* Uninteresting remaining cases *)
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
  In order to proof the termination we need to find a measure function, 
  but then the problem is to prove the termination of this counting function as well.
 *)

subsection\<open>Attempts to prove termination\<close>
text\<open>We spent quite a lot of time trying to prove the termination of the above function.
What follows are some of our efforts. Although termination is ultimately not proven, 
the function computes and by looking at some non-trivial examples we find that it 
does what it is supposed to.
\<close>
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
  (* so close! *)*)
sorry

termination congru
apply (relation "measure (
\<lambda>x. case x of 
  Inl (a,b) 
    \<Rightarrow> (Max({depth a, depth b})) 
| Inr (a,b,c) 
    \<Rightarrow> max (maxl (map depth (a))) (maxl (map depth (b@c))) )")
apply auto
sorry

subsection\<open>Examples of structural congruence\<close>
value "((One\<parallel>Two)\<parallel>(Three\<parallel>Four))\<parallel>Null =C ((One\<parallel>Three)\<parallel>(Two\<parallel>Four))"
value "(((zero\<leftarrow>zero.\<^bold>0.) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) =C (((zero\<leftarrow>zero.\<^bold>0.) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) \<parallel> \<^bold>0)"
value "(( \<^bold>0 \<parallel> (n\<^sub>1\<triangleleft>\<^bold>0 \<parallel> \<^bold>0\<triangleright>)) =C (n\<^sub>1\<triangleleft>\<^bold>0\<triangleright>))"

theorem example:
shows "(((zero\<leftarrow>zero.\<^bold>0.) \<parallel> \<^bold>0) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) =C (((zero\<leftarrow>zero.\<^bold>0.) \<parallel> (zero\<leftarrow>zero.\<^bold>0.)) \<parallel> \<^bold>0)"
by simp

value "getList ((a \<parallel> b) \<parallel> c)"

declare [[ smt_timeout = 20 ]]

subsection\<open>Structural congruence is an equivalence relation\<close>
text\<open>Proofs unfortunately not completeted\<close>
abbreviation reflexive
  where "reflexive \<equiv> \<lambda> R. \<forall> r. R r r"
abbreviation transitive
  where "transitive \<equiv> \<lambda> R. \<forall> x. \<forall> y. \<forall> z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation symmetric
  where "symmetric \<equiv> \<lambda> R. \<forall> x. \<forall> y. R x y \<longrightarrow> R y x"

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
  shows "(eq2 a a [])"
sorry

theorem eqSymmetric:
  shows "\<forall> a b. (eq2 a b [] \<longrightarrow> eq2 b a [])"
sorry

theorem eqTransitive:
  shows "\<forall> a b c. (((eq2 a b []) \<and> (eq2 b c [])) \<longrightarrow> (eq2 a c []))"
sorry

theorem parAssoc:
  shows "((a\<parallel>b)\<parallel>c) =C (a\<parallel>(b\<parallel>c))"
using congruReflexive eqReflexive by (induction a, auto)

theorem parCommutative:
  shows "a\<parallel>b =C b\<parallel>a"
using congruReflexive eqReflexive  apply (induction a rule: P.induct)
apply simp
apply (induction b rule: P.induct, auto)
using congruSymmetric apply blast
sorry

theorem zeroLeft:
  shows "(Null \<parallel> a) =C a"
using congruReflexive apply (induction a rule: P.induct, auto)
apply (simp add: congruReflexive)
by (simp add: eqReflexive)


theorem zeroRight:
  shows "(a \<parallel> Null) =C a"
apply (induction a rule: P.induct, auto)
apply (simp add: congruReflexive)
apply (simp add: congruReflexive)
by (simp add: eqReflexive)

end