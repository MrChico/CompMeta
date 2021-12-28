theory  LundfallErfurtEx07
imports QML Main

begin

section "Exercise 1"

theorem surj_theorem: "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  hence "\<exists>a. {x. x \<notin> f x} = f a" by blast
  thus "False" by blast
qed

theorem inj_theorem: "\<not>inj(f :: 'a set \<Rightarrow> 'a)"
proof
  fix A
  assume 0: "inj f"
  hence "\<forall> a. \<forall> b. ((f(a) \<noteq> f(b)) \<longrightarrow> (a \<noteq> b))" (* by (simp add: surj_f_inv_f) *)
sorry







(*
abbreviation andrews_equality :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "=A" 43)
*)

(*
abbrevationdd
*)

end