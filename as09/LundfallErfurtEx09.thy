theory LundfallErfurtEx09
imports QMLS5U Main
begin
section\<open>Exercise 2\<close>

(*S5 is axiom M together with axiom V*)

theorem M:
  shows "\<lfloor>\<^bold>\<box>p\<^bold>\<rightarrow>p\<rfloor>"
  by simp

theorem V:
  shows "\<lfloor>\<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>"
  by simp
  
  (*Positive property*)
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  (* A God-like being possesses all positive properties. *)
  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<^bold>\<forall>(\<lambda>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<Phi> x))"   

  (* An essence of an individual is a property possessed by it 
     and necessarily implying any of its properties *)
  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi> x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi> y \<^bold>\<rightarrow> \<Psi> y))"

  (* Necessary existence of an individual is the necessary 
     exemplification of all its essences. *)
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<Phi>))"


  axiomatization where
    (* Either a property or its negation is positive, but not both. *)
    A1a: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>(P \<Phi>)\<rfloor>" and
    A1b: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<not>(P \<Phi>) \<^bold>\<rightarrow> P (\<^sup>\<not>\<Phi>)\<rfloor>" and

    (* A property necessarily implied by a positive property is positive. *)
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>. (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>x. \<Phi> x \<^bold>\<rightarrow> \<Psi> x)) \<^bold>\<rightarrow> P \<Psi>\<rfloor>"
  axiomatization where A3:  "\<lfloor>P G\<rfloor>" 
  axiomatization where A4:  "\<lfloor>\<^bold>\<forall>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>(P \<Phi>)\<rfloor>" 
  axiomatization where A5:  "\<lfloor>P NE\<rfloor>"

theorem god:
  shows "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G)\<rfloor>"
  by (metis A1a A1b A2 A3 A4 A5 G_def NE_def ess_def) 

subsection\<open>d\<close>
text \<open>With this formalization, there is no difference between a proposition being globally valid
and it being necessarily true. In fact, for any world w, we have "\<lfloor>P\<rfloor> = \emph{\box}P(w)"\<close>
end
