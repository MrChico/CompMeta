theory namespace_logic
imports Main spatial
begin

(*Type of formulae in namespace logic*)
datatype F = true
  | false
  | negation F ("\<not>_")
  | conjunction F F ("_&_" 80)
  | separation F F ("_\<parallel>_" 80)
  | descent P ("\<acute>_`" 80)
  | elevation a P ("_\<triangleleft>_\<triangleright>" 80)
  | activity a n P ("\<langle>_?_\<rangle>" 80)
  | maxFixPoint F F ("rec_._" 80)
  | quantification n F F ("\<forall>_:_._")
  and a = indication ("`_\<acute>")
  | n

fun evalFormula "set P \<Rightarrow> F \<Rightarrow> set P"
  where "evalFormula _ true = _"
    | 
  

end