theory LundfallErfurtEx06
imports QML Main

begin
text \<open>Exercise 1\<close>
consts X :: \<sigma>
consts Y :: \<sigma>
theorem K:
  shows "\<lfloor> \<^bold>\<box>(X \<^bold>\<rightarrow> Y) \<^bold>\<rightarrow> (\<^bold>\<box> X \<^bold>\<rightarrow> \<^bold>\<box> Y)\<rfloor>"
proof simp
qed

consts "mayVote" :: "\<mu>\<Rightarrow>\<sigma>"
consts "bornEqual" :: "\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"

theorem Ex1:
  assumes 1: "\<lfloor> \<^bold>\<not> \<^bold>\<diamond> ((\<^bold>\<forall> h1. \<^bold>\<forall> h2. bornEqual h1 h2) \<^bold>\<and> (\<^bold>\<exists> h3. \<^bold>\<not> mayVote(h3)))  \<rfloor>" AND (*Not possible (all humans born equal AND some humans MAY NOT vore)*)
  assumes 2: "\<lfloor> \<^bold>\<box> (\<^bold>\<forall> h1. \<^bold>\<forall> h2. bornEqual h1 h2) \<rfloor>" (*all are born equal*)
  shows "\<lfloor> (\<^bold>\<box> (\<^bold>\<forall> h.(mayVote(h)))) \<rfloor>"
proof -
 from assms have "\<lfloor> \<^bold>\<box> (\<^bold>\<not> ((\<^bold>\<forall> h1. \<^bold>\<forall> h2. bornEqual h1 h2) \<^bold>\<and> (\<^bold>\<exists> h3. \<^bold>\<not> mayVote(h3)))) \<rfloor>" by simp
 then have "\<lfloor> \<^bold>\<box> ((\<^bold>\<forall> h1. \<^bold>\<forall> h2. bornEqual h1 h2) \<^bold>\<rightarrow> (\<^bold>\<not> (\<^bold>\<exists> h3. \<^bold>\<not> mayVote(h3)))) \<rfloor>" by auto
 then have 3: "\<lfloor> (\<^bold>\<box> (\<^bold>\<forall> h1. \<^bold>\<forall> h2. (bornEqual h1 h2))) \<^bold>\<rightarrow> (\<^bold>\<box> \<^bold>\<not> (\<^bold>\<exists> h3. \<^bold>\<not> mayVote(h3))) \<rfloor>" using K by simp
 from 2 3 have "\<lfloor>(\<^bold>\<box> \<^bold>\<not> (\<^bold>\<exists> h3. \<^bold>\<not> mayVote(h3)))\<rfloor>" by simp
 then show ?thesis by simp
qed

end