theory NameEquiv
imports RhoCalc
begin

section\<open>Name equivalence\<close>
text\<open>Similarly to structural congruence, we build up an equivalence of names:
To quote an unquoted name n gives n back:
\begin{equation}
n \equiv_N \left\ulcorner \left\urcorner n \right\ulcorner \right\urcorner.
\end{equation}
Furtermore, the quotations of two structurally equivalent processes are name equivalent \<close>

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

text\<open>Some examples\<close>
value "`\<acute>zero`\<acute> =N zero"
value "`\<acute>`\<acute>zero`\<acute>`\<acute> =N zero"
value "newName 3 =N three"
value "newName 3 =N zero"
value "three =N newName 3"
value "`((One\<parallel>Two)\<parallel>(Three\<parallel>Four))\<parallel>Null\<acute> =N `((One\<parallel>Three)\<parallel>(Two\<parallel>Four))\<acute>"
value "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"
theorem testNameEQ1:
  shows "`p \<parallel> (\<^bold>0 \<parallel> q)\<acute> =N `q \<parallel> p\<acute>"
using parCommutative by auto

subsection\<open>Proof of equivalence relation\<close>
text\<open>Reflexivity and symmetry is proven: only transitivity is unfinished. 
(It also relies on unfinished proofs of structural congruence)
\<close>

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
(* I dont know how to make an induction argument here which runs over all three variables
using assms apply (induct a c rule: name_equivalence.induct)
apply auto
apply (simp add: assms congruTransitive eqTransitive)
*)
sorry

end