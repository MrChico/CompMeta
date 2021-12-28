theory Scratch
imports Main "~~/src/HOL/Library/Multiset"
begin

abbreviation A where "A \<equiv> (1::nat)#(2::nat)#(3::nat)#[]"
abbreviation B where "B \<equiv> (5::nat)#(2::nat)#(3::nat)#[]"


abbreviation reflexiveR
  where "reflexiveR \<equiv> \<lambda> R. \<forall> r. R r r"
abbreviation transitiveR
  where "transitiveR \<equiv> \<lambda> R. \<forall> x. \<forall> y. \<forall> z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation symmetricR
  where "symmetricR \<equiv> \<lambda> R. \<forall> x. \<forall> y. R x y \<longrightarrow> R y x"

fun even:: "nat \<Rightarrow> bool"
  where "even 0 = True"
       |"even (Suc(0)) = False"
       |"even (Suc(Suc(n))) = even(n)"

abbreviation congru (infixl "=C" 52)
  where "congru \<equiv> \<lambda> a b. ((even a) = (even b))" 


function eq :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
     and lminus :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
     and inC :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  where "eq [] []   = True"
       |"eq [] (x#xs) = eq (x#xs) []"
       |"eq (x#xs) bs = (if (inC x bs) then (eq xs (lminus x bs)) else False)"
       |"inC a [] = (a =C 0)"
       |"inC a (x#xs) = ((a =C x) \<or> (inC a xs))"
       |"lminus a [] = []"
       |"lminus a (x#xs) = (if (a =C x) then xs else (x#(lminus a xs)))"
sorry
termination
sorry

function eq2 :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where 
  "eq2 [] [] [] = True"
  |"eq2 (x#xs) [] [] = False"
  |"eq2 (x#xs) [] (b#bs) = False"
  |"eq2 [] [] (a#as) = False"
  |"eq2 [] (b#bs) _ = False"
  |"eq2 (x#xs) (y#ys) zs = (if (x =C y) then (eq2 xs (zs@ys) []) else (eq2 (x#xs) ys (y#zs)))"


value "eq2 ((2::nat)#[]) ((2::nat)#[]) []"
value "eq2 A B []"

theorem reflexivCongru:
  shows "reflexiveR eq"
sorry

theorem transitiveCongru:
  shows "transitiveR eq"
sorry

theorem symmetricCongru:
  shows "symmetricR eq"
sorry

value "eq A B"

primrec omg :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "omg 0 b \<equiv> True"
 |"omg a b \<equiv> False"

end