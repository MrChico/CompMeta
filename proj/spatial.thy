theory spatial
imports Main
begin

(*The mutually recursive datatypes of processes and names*)
datatype P = Null | input n n P | lift n P | drop n | par P P  
  and n = quote P

(*Structural congruence*)

primrec congr :: "P \<Rightarrow> P \<Rightarrow> bool" (infixr "=S" 65) where
  "par Null p =S par p Null = true" |
  "par q p =S par p q = true" 
  (*
  "(x # xs) @ ys = x # (xs @ ys)"*)

primrec congr :: "P \<Rightarrow> P \<Rightarrow> bool" where
  par Null _ = true  

end