section \<open>A Hilbert Proof Calculus for Propositional Logic (PL)\<close>

(*<*)
theory Hilbert
imports Main

begin
(*>*)

subsection \<open>Logical Connectives for PL\<close>

subsubsection \<open>Primitive Connectives\<close>

consts impl :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<rightarrow>" 49)
consts not :: "bool \<Rightarrow> bool" ("\<^bold>\<not>")

text \<open>In philosophy, we often assume that the only two logical connectives
  are the implication @{const impl} and the negation @{const not}.
  This is handy, since it simplifies proofs to only consider these two
  cases.
\<close>

subsubsection \<open>Further Defined Connectives\<close>

text \<open>We can of course add further connectives that are to be
  understood as abbreviations that are defined in terms of the primitive
  connectives above.\<close>

abbreviation disj :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<or>"50) where
  "A \<^bold>\<or> B \<equiv> \<^bold>\<not>A \<^bold>\<rightarrow> B"
abbreviation conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<and>"51) where
  "A \<^bold>\<and> B \<equiv> \<^bold>\<not>(A \<^bold>\<rightarrow> \<^bold>\<not>B)"

subsection \<open>Hilbert Axioms for PL\<close>

subsubsection \<open>Axiom Schemes\<close>

axiomatization where
  (* A1: "(A \<^bold>\<rightarrow> A)" and*)
  A2: "A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)" and
  A3: "(A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> C)) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> C))" and
  A4: "(\<^bold>\<not>A \<^bold>\<rightarrow> \<^bold>\<not>B) \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)"

subsubsection \<open>Inference Rules\<close>

axiomatization where
  ModusPonens: "(A \<^bold>\<rightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"

(* Test soundness of axiomatizaion *)
lemma True nitpick [satisfy, user_axioms, expect = genuine] oops

subsection \<open>A Proof\<close>

(* just playing around *)
thm A3[where A = "A" and B = "(B \<^bold>\<rightarrow> A)" and C = "A"]
thm A3[of "A" "(B \<^bold>\<rightarrow> A)" "A"]

text \<open>We show that A1 is redundant\<close>

theorem A1Redundant:
  shows "A \<^bold>\<rightarrow> A"
proof -
  have 1: "(A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> ((A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A))" by (rule A3[where B = "(B \<^bold>\<rightarrow> A)" and C = "A"])
  have 2: "A \<^bold>\<rightarrow> ((B \<^bold>\<rightarrow> A) \<^bold>\<rightarrow> A)"  by (rule A2[where B = "B \<^bold>\<rightarrow> A"])
  from 1 2 have 3: "(A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> A)" by (rule ModusPonens)
  have 4: "(A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> A))" by (rule A2)
  from 3 4 have 5: "A \<^bold>\<rightarrow> A" by (rule ModusPonens)
  thus ?thesis .
qed


theorem 
  shows "A \<^bold>\<rightarrow> A"
  by (metis (full_types) A2 ModusPonens) -- "Sledgehammer even finds a proof without using A3"

subsection \<open>Exercise 3\<close>

theorem transitivity:
  assumes 1: "A \<^bold>\<rightarrow> B" and
  2: "B \<^bold>\<rightarrow> C"
  shows "A \<^bold>\<rightarrow> C"
  proof -
    have 3: "(A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> C)) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> C)" by (rule A3)
    have 4: "(B \<^bold>\<rightarrow> C) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> C))" by (rule A2)
    from 4 2 have 5: "A \<^bold>\<rightarrow> (B \<^bold>\<rightarrow> C)" by (rule ModusPonens)
    from 3 5 have 6: "(A \<^bold>\<rightarrow> B) \<^bold>\<rightarrow> (A \<^bold>\<rightarrow> C)" by (rule ModusPonens)
    from 6 1 have 7: "A \<^bold>\<rightarrow> C" by (rule ModusPonens)
    thus ?thesis .
qed
(*<*)
end
(*>*)
