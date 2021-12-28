theory Something
imports Main 

begin

(*

definition xor2 :: "Bool \<Rightarrow> Bool \<Rightarrow> Bool" (infixl ) 

*)
 
abbreviation xor (infixl "\<oplus>" 40) where
  "a \<oplus> b \<equiv> (\<not> a \<and> b) \<or> (a \<and> \<not> b)"

fun f :: "nat \<Rightarrow> nat" where 
  "f 0 = 0" |
  "f (Suc 0) = 5" |
  "f _ = 0"

value "f 1"


function f2 where
  "f2 0 = 0" |
  "f2 1 = 5" |
  "f2 _ = 0"
oops

datatype restrictedBurger = buns 
  |Meat restructedBurger 
  |Cabbage restrictedBurger

value "Meat (Meat (Cabbage buns))"

datatype 'a burger = Ingredient 'a "'a burger" | buns
value "Ingredient 5 buns"

typedecl ingredients

consts 
  meat :: ingredients
  lattuce :: ingredients
  sauce :: ingredients
  cheese :: ingredients
  tofu :: ingredients

fun size :: "'a burger \<Rightarrow> nat" where
  "size buns = 0" |
  "size (Ingredient _ rest) = 1 + (size rest)"

fun stack :: "'a burger \<Rightarrow> 'a burger \<Rightarrow> 'a burger" where
  "stack buns b = b" |
  "stack (Ingredient i rest)  b = Ingredient i(stack rest b)"

lemma "size (stack a b) = size a + size b"
  proof (induct a)
    case ia: buns
      have "size (stack buns b) = size b" by simp
      have "\<dots> = 0 + size b" by simp
      have "\<dots> = size buns + size b" by simp
      thus ?case by simp
  next
    case iv: (Ingredient i rest)
      have "size (stack (Ingredient i rest) b) = 1 + size (stack rest buns)" by simp
      have "\<dots> = 1 + (size rest + size b)" using iv by simp
      have "\<dots> = size (Ingredient i rest) + size b" by simp
      thus ?case using iv by simp
end
