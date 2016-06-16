(* Christoph Benzmüller and Bruno Woltzenlogel-P., February 2016 *)

theory Scott
imports QML

begin
  (* Gödel's Ontological Argument: Variant of Scott *)

  (* We work in logic S5. *) 
  axiomatization where S5: "S5_sem" 


  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  axiomatization where
    (* Either a property or its negation is positive, but not both. *)
    A1a: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>(P \<Phi>)\<rfloor>" and
    A1b: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<not>(P \<Phi>) \<^bold>\<rightarrow> P (\<^sup>\<not>\<Phi>)\<rfloor>" and

    (* A property necessarily implied by a positive property is positive. *)
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>. (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>x. \<Phi> x \<^bold>\<rightarrow> \<Psi> x)) \<^bold>\<rightarrow> P \<Psi>\<rfloor>"

  (* Positive properties are possibly exemplified. *)
  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists> \<Phi>)\<rfloor>"  
  sledgehammer
  using A1a A2 by blast

  (* A God-like being possesses all positive properties. *)
  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<^bold>\<forall>(\<lambda>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<Phi> x))"   

  (* The property of being God-like is positive. *)
  axiomatization where A3:  "\<lfloor>P G\<rfloor>" 

  (* Possibly, God exists. *)
  corollary C: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists> G)\<rfloor>" 
  sledgehammer
  by (simp add: A3 T1)

  (* Positive properties are necessarily positive). *)
  axiomatization where A4:  "\<lfloor>\<^bold>\<forall>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box>(P \<Phi>)\<rfloor>" 

  (* An essence of an individual is a property possessed by it 
     and necessarily implying any of its properties *)
  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi> x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi> y \<^bold>\<rightarrow> \<Psi> y))"

  (* Being God-like is an essence of any God-like being. *)
  theorem T2: "\<lfloor>\<^bold>\<forall>(\<lambda>x. G x \<^bold>\<rightarrow> G ess x)\<rfloor>"
  sledgehammer [provers = remote_leo2, verbose]
  by (metis A1b A4 G_def ess_def)

  (* Necessary existence of an individual is the necessary 
     exemplification of all its essences. *)
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<Phi>))"

  (* Necessary existence is a positive property *)
  axiomatization where A5:  "\<lfloor>P NE\<rfloor>"

  (* Necessarily, God exists *) 
  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists> G)\<rfloor>"   
  sledgehammer [provers = remote_leo2, verbose] 
  by (metis A5 C T2 S5 G_def NE_def)

  (* God exists *)
  corollary C2: "\<lfloor>\<^bold>\<exists> G\<rfloor>"  
  sledgehammer [provers = remote_leo2, verbose]
  by (metis T1 T3 G_def S5)

  (* The consistency of the entire theory is confirmed by Nitpick. *)
  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops

  (* G\"odel's God is flawless: (s)he does not have non-positive properties. *)
  theorem Flawlessness: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<forall>x. (G x \<^bold>\<rightarrow> (\<^bold>\<not>(P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<Phi> x)))\<rfloor>"
  sledgehammer [provers = remote_leo2, verbose]
  by (metis A1b G_def) 
  
  (* There is only one God: any two God-like beings are equal. *)   
  theorem Monotheism: "\<lfloor>\<^bold>\<forall>x.\<^bold>\<forall>y. (G x \<^bold>\<rightarrow> (G y \<^bold>\<rightarrow> (x \<^bold>=\<^sup>L y)))\<rfloor>"
  sledgehammer [provers = remote_satallax, verbose]
  by (metis Flawlessness G_def)
 

  (* Modal Collapse *)
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"  
  sledgehammer [provers = remote_satallax, verbose, timeout = 600] 
  -- {* by (metis T2 T3 ess\_def) *}
  -- {* by (meson T2 T3 ess_def) *}
  oops

(*<*) 
end
(*>*) 