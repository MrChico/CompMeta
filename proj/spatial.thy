theory spatial
imports Main
begin

(*The mutually recursive datatypes of processes and names*)
datatype P = Null             ("\<^bold>0")
           | input n n P      ("_\<leftarrow>_._" 60)
           | lift n P         ("_\<triangleleft>_\<triangleright>" 20)
           | drop n           ("\<acute>_`" 30)
           | par P P          (infixl "\<parallel>" 51)    
     and n = quote P          ("`_\<acute>")

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


(*substitution*)
(*Takes a process, specifies the names to be substituted and returns a process*)
function sn :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n" where
  "sn `x\<acute> `q\<acute> `p\<acute> = (if (`x\<acute> =N `p\<acute>) then `q\<acute> else `x\<acute>)" 
  
primrec s :: "P \<Rightarrow> n \<Rightarrow> n \<Rightarrow> P" where
  "s \<^bold>0 _ _ = \<^bold>0" |
  "s (R \<parallel> S) q p = s R q p \<parallel> s S q p" |
  "s x\<leftarrow>y.R q p = (sn x q p)\<leftarrow>z.(s ((s R z y) q p))" 

end