theory LundfallErfurtEx09
imports QMLS5U Main Temp
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
  consts Pp :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  (* A God-like being possesses all positive properties. *)
  definition God :: "\<mu> \<Rightarrow> \<sigma>" where "God = (\<lambda>x. \<^bold>\<forall>(\<lambda>\<Phi>. Pp \<Phi> \<^bold>\<rightarrow> \<Phi> x))"   

  (* An essence of an individual is a property possessed by it 
     and necessarily implying any of its properties *)
  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi> x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi> y \<^bold>\<rightarrow> \<Psi> y))"

  (* Necessary existence of an individual is the necessary 
     exemplification of all its essences. *)
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<Phi>))"


  axiomatization where
    (* Either a property or its negation is positive, but not both. *)
    A1a: "\<lfloor>\<^bold>\<forall>\<Phi>. Pp(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>(Pp \<Phi>)\<rfloor>" and
    A1b: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<not>(Pp \<Phi>) \<^bold>\<rightarrow> Pp (\<^sup>\<not>\<Phi>)\<rfloor>" and

    (* A property necessarily implied by a positive property is positive. *)
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>. (Pp \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>x. \<Phi> x \<^bold>\<rightarrow> \<Psi> x)) \<^bold>\<rightarrow> Pp \<Psi>\<rfloor>"
  axiomatization where A3:  "\<lfloor>Pp God\<rfloor>" 
  axiomatization where A4:  "\<lfloor>\<^bold>\<forall>\<Phi>. Pp \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>(Pp \<Phi>)\<rfloor>" 
  axiomatization where A5:  "\<lfloor>Pp NE\<rfloor>"

theorem god:
  shows "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> God)\<rfloor>"
  by (metis A1a A1b A2 A3 A4 A5 God_def NE_def ess_def) 

subsection\<open>d\<close>
text \<open>With this formalization, there is no difference between a proposition being globally valid
and it being necessarily true. In fact, for any world w, we have "\<lfloor>P\<rfloor> = \emph{\box}P(w)"\<close>

section\<open>Exercise 3\<close>
subsection\<open>(a)\<close>
theorem "KforG":
assumes "*\<lfloor> G (\<Psi> *\<rightarrow> \<Phi>) \<rfloor>*"
shows "*\<lfloor> G \<Psi> *\<rightarrow> G \<Phi> \<rfloor>*"
  by (simp add: assms)

theorem "KforH":
assumes "*\<lfloor> H(\<Psi> *\<rightarrow> \<Phi>) \<rfloor>*"
shows "*\<lfloor> H \<Psi> *\<rightarrow> H \<Phi> \<rfloor>*"
  by (simp add: assms)

theorem "SymI":
shows "*\<lfloor> \<Psi> *\<rightarrow>  G (P \<Psi>) \<rfloor>*"
  by auto

theorem "SymII":
shows "*\<lfloor> \<Psi> *\<rightarrow>  H (F \<Psi>) \<rfloor>*"
 by auto

theorem TRAN:
  assumes Kt_sem
  shows "*\<lfloor>G \<Psi> *\<rightarrow> G(G \<Psi>)\<rfloor>*"
  using assms by blast

theorem NOEND:
  assumes Kt_sem
  shows "*\<lfloor> G \<Psi> *\<rightarrow> F \<Psi>\<rfloor>*"
  using assms by blast

theorem NOBEG:
  assumes Kt_sem
  shows "*\<lfloor> H \<Psi> *\<rightarrow> P \<Psi>\<rfloor>*"
  using assms by blast

theorem LIN:
  assumes "Kt_sem"
  shows "*\<lfloor> (P (F \<Psi>) *\<or> F (P \<Psi>)) *\<rightarrow> (P \<Psi>) *\<or> \<Psi> *\<or> (F \<Psi>) \<rfloor>*"
  using assms by blast

subsection\<open>(c)\<close>
consts dead :: "\<mu>\<mu> \<Rightarrow> \<sigma>\<sigma>"
theorem deadness:
  assumes "Kt_sem \<and> *\<lfloor> *\<forall> entity.  (dead(entity) *\<rightarrow> G dead(entity)) *\<and> F dead(entity) *\<and> (F *\<not> dead(entity) *\<or> P *\<not> dead(entity) *\<or> *\<not> dead(entity)) \<rfloor>*"
  shows "*\<lfloor> *\<forall> entity. P (H *\<not> dead(entity)) \<rfloor>*"
  by (metis assms)

end
