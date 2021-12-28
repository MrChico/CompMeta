theory kosmale_project
imports Main
begin

declare [[syntax_ambiguity_warning = false]]

(* A partial formalization of CCS, the calculus of communicating systems
 * based on the script of the "Nebenläufige Programmierung" lecture
 * a somewhat outdated version of it can be found at "http://pseuco.de/downloads/np.pdf"
 * (but afaik Felix, who also worked on this topic did send you a more recent version anyway)
 * Some inspiration (mainly regarding the notation) was taken from http://maude.sip.ucm.es/~alberto/esf/CCS-Isabelle.thy
 * Some details were discussed with Felix Freiberger
*)

type_synonym ( 'q, 'l ) transition = "'q \<Rightarrow> 'l \<Rightarrow> 'q \<Rightarrow> bool"


(* CCS *)

(* An important part of CCS are actions: They are partitioned in communication actions
 * (with Excl/Qucl) and the internal action \<tau>
 *)
datatype action =
 Excl string ("!")|
 Qucl string ("?")|
 Tau ("\<tau>")

value "!''a''"
value "?''b''"
value "\<tau>"

(* compl returns the complementary action of a communication action
 * which is useful for synchronization as we'll see later
 * for internal actions the behaviours is undefined
 *)
fun compl:: "action \<Rightarrow> action" where
"compl (Excl a) = Qucl a" |
"compl (Qucl a) = Excl a" |
"compl \<tau> = undefined"

(* support for the Restriction operator *)
fun in_kom:: "action \<Rightarrow> bool" where
"in_kom \<tau> = False" |
"in_kom _ = True"

fun restricted :: "action \<Rightarrow> string set \<Rightarrow> bool" where
"restricted (Excl a) H = (a \<in> H)" |
"restricted (Qucl a) H = (a \<in> H)" |
"restricted \<tau> _ = False"

value "in_kom (!''a'')"

type_synonym variable = string

(* The syntax of CCS *)
datatype process =
  Stop ("0") |
  Prefix action process  ("_ \<cdot> _" [120, 110] 110) |
  Plus process process (infixl "+ccs" 85) |
  Par process process (infixl "\<bar>" 90) |
  Rec variable |
  Res process "string set" ("_ \<setminus> _" [100, 120] 100)

type_synonym transition_triple = "process \<times> action \<times> process"
type_synonym transition_relation = "transition_triple set"
type_synonym state = "process"
type_synonym states = "process set"
type_synonym initial_state = process
type_synonym LTS = "(states \<times> transition_relation \<times> initial_state)"

type_synonym Transition = "(process, action) transition"
  
type_synonym env = "variable \<Rightarrow> process option"   

text{*
  Now we define the semantic of the CCS processes.
  The predicate is called LTS because if one connects the processes with their successor states
  and puts the action labels on the edges, a LTS is yielded.
*}


inductive LTS :: "env \<Rightarrow> Transition" ("(_/ \<Turnstile>  _/ - _/ \<rightarrow> _)"  [0, 0, 0, 61] 61)  where 
prefix: " LTS \<Gamma> (\<alpha> \<cdot> P)  \<alpha>  P" |
choice_l: "LTS \<Gamma> P1 \<alpha> P1' \<Longrightarrow>  LTS \<Gamma>  (P1 +ccs P2)  \<alpha>  P1'" |
choice_r: "LTS \<Gamma> P2 \<alpha> P2' \<Longrightarrow>  LTS \<Gamma> (P1 +ccs P2) \<alpha> P2'" |
par_l: "LTS \<Gamma> P1 \<alpha> P1' \<Longrightarrow> LTS  \<Gamma> (P1 \<bar> P2) \<alpha> (P1' \<bar> P2) " |
par_r: "LTS \<Gamma> P2 \<alpha> P2' \<Longrightarrow> LTS  \<Gamma> (P1 \<bar> P2) \<alpha> (P1 \<bar> P2')" |
sync: "\<lbrakk>in_kom a; LTS \<Gamma>  P1 a  P1'; LTS \<Gamma>  P2  (compl a) P2' \<rbrakk> \<Longrightarrow>  LTS \<Gamma> (P1 \<bar> P2) \<tau> (P1' \<bar> P2')" |
res: "\<lbrakk>\<not> (restricted a H); LTS \<Gamma> P a P' \<rbrakk> \<Longrightarrow> LTS \<Gamma> (P \<setminus> H) a (P' \<setminus> H)" |
rec: "\<lbrakk> (\<Gamma> X) = Some P; LTS \<Gamma> P a P'\<rbrakk> \<Longrightarrow> LTS \<Gamma> (Rec X) a P'"

declare LTS.intros [intro]
thm LTS.induct

inductive_cases prefixE[elim!]: " LTS \<Gamma> (\<alpha> \<cdot> P)  \<alpha>  P"
inductive_cases choice_lE[elim!]: "LTS \<Gamma>  (P1 +ccs P2)  \<alpha>  P1'"
inductive_cases choice_rE[elim!]: "LTS \<Gamma> (P1 +ccs P2) \<alpha> P2'"
inductive_cases par_lE[elim!]: "LTS  \<Gamma> (P1 \<bar> P2) \<alpha> (P1' \<bar> P2)"
inductive_cases par_rE[elim!]: "LTS  \<Gamma> (P1 \<bar> P2) \<alpha> (P1 \<bar> P2')"
inductive_cases syncE[elim!]: "LTS \<Gamma> (P1 \<bar> P2) \<tau> (P1' \<bar> P2')"
inductive_cases resE[elim!]: "LTS \<Gamma> (P \<setminus> H) a (P' \<setminus> H)"
inductive_cases recE[elim!]: "LTS \<Gamma> (Rec X) a P'"

code_pred LTS .

fun x_to_a_stop :: env where
"x_to_a_stop ''X'' = Some (!''a'' \<cdot> Stop)" |
"x_to_a_stop x = None"

(* commented out, because it is slow *)
(* value "\<Gamma> \<Turnstile>  !''a''.Stop - !''a'' \<rightarrow> Stop" (* True *)
value "\<Gamma> \<Turnstile>  !''a''.Stop \<setminus> {''a''} - \<alpha> \<rightarrow> Stop" (* False *)
value "\<Gamma> \<Turnstile> (!''a''.Stop \<bar> ?''a''.Stop) - \<tau> \<rightarrow> Stop \<bar> Stop" (* True *) *)
value "x_to_a_stop \<Turnstile> (Rec ''X'') - !''a'' \<rightarrow> Stop" (* True *)


(* a few lemmas to show that the semantic is working as expected *)
lemma trans_no_stop[simp]: "(\<Gamma> \<Turnstile>  P - a \<rightarrow> P') \<Longrightarrow> P \<noteq> Stop" proof(induction rule: LTS.induct)
qed(auto)

lemma stop_no_trans[simp]: "(\<Gamma> \<Turnstile>  Stop - a \<rightarrow> P') \<Longrightarrow> False" proof(-)
 assume "(\<Gamma> \<Turnstile>  Stop - a \<rightarrow> P')"
 then show "False" using trans_no_stop by  blast
qed

lemma stop_choice_neutral: "(\<Gamma> \<Turnstile> (P +ccs Stop) - a \<rightarrow> P') \<longleftrightarrow> (\<Gamma> \<Turnstile> P - a \<rightarrow> P')"
proof
  assume "\<Gamma> \<Turnstile>  P +ccs Stop - a \<rightarrow> P'"
  then show "(\<Gamma> \<Turnstile> P - a \<rightarrow> P')" using stop_no_trans by blast
  next
  assume "\<Gamma> \<Turnstile>  P - a \<rightarrow> P'"
  then show "\<Gamma> \<Turnstile>  P +ccs Stop - a \<rightarrow> P'" by blast
qed

lemma [simp]: "(\<Gamma> \<Turnstile> (P +ccs Stop) - a \<rightarrow> P') \<longrightarrow> (\<Gamma> \<Turnstile> P - a \<rightarrow> P')"
using stop_choice_neutral by auto

(* In the following section a number of equivalence relations are defined
  (in the end only three, due to  a lack of time)
  Before that, the concepts of Reachability and Traces are introduced
  
  A state is reachable from another one if there exists a path between them
  which can be justified by the CCS semantic.
  
  The traces of a process are a subset of Act*. They are obtained by considering valid paths 
  according to the semantic and concatenating the  projection of the actions from the edges.
*)

(* it's still called TraceHelper, but now it's also used for Reachability *)
inductive TraceHelper :: "env \<Rightarrow> process \<Rightarrow> process \<Rightarrow> action list \<Rightarrow> bool" where
base: "TraceHelper \<Gamma> P P []" |
step: "\<lbrakk> TraceHelper \<Gamma> P P' as; \<Gamma> \<Turnstile> P' - \<alpha> \<rightarrow> P'' \<rbrakk> \<Longrightarrow> TraceHelper \<Gamma> P P' (as@[\<alpha>])"

declare TraceHelper.intros [intro]
thm TraceHelper.induct
inductive_cases traceh_baseE[elim]: "TraceHelper \<Gamma> P P []"
inductive_cases traceh_stepE[elim]: "TraceHelper \<Gamma> P P (as@[a])"

inductive Traces :: "env \<Rightarrow> process \<Rightarrow> action list \<Rightarrow> bool" where
"TraceHelper \<Gamma> P P' as \<Longrightarrow> Traces \<Gamma> P as"

declare Traces.intros [intro]
thm Traces.induct
inductive_cases trace_baseE[elim]: "Traces \<Gamma> P  []"
inductive_cases trace_stepE[elim]: "Traces \<Gamma> P (as@[a])"


inductive Reach :: "env \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool" where
"TraceHelper \<Gamma> P P' as  \<Longrightarrow> Reach \<Gamma> P P''"

declare Reach.intros[intro]
thm Reach.induct
inductive_cases reachE[elim]: "Reach \<Gamma> P P'"


(* Our first equality: trace equality: Two processes are equal if their traces are equal *)
abbreviation trace_equiv :: "env \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool" where
  "trace_equiv \<Gamma> P P' \<equiv> (\<forall> traces. (Traces \<Gamma> P traces) \<longleftrightarrow> (Traces \<Gamma> P' traces))"

(* trace_equiv is an equivalence relation *)
  
lemma reflp_traces : "reflp (trace_equiv \<Gamma>)"
  unfolding reflp_def by auto

lemma symp_traces: "symp (trace_equiv \<Gamma>)"
  unfolding symp_def by simp
  
lemma trans_traces: "transp (trace_equiv \<Gamma>)"
  unfolding transp_def by force
  
(* Our second equality: isomorphy: Two process are equal if their is bijection f between
   their states, such that the initial states are mapped to one another and
   whenever s -a\<rightarrow> s', f(s) -a\<rightarrow> f(s') and vice versa
*)

abbreviation isomorph :: "env \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool" where
  "isomorph \<Gamma> P P' \<equiv> (\<exists> f::process \<Rightarrow> process. bij f \<and> (f P = P') \<and> ( \<forall> P'' P''' \<alpha>.
    (
    ( (Reach \<Gamma> P P'') \<and> (\<Gamma> \<Turnstile> P'' -\<alpha> \<rightarrow> P''')) \<longleftrightarrow> 
      (Reach \<Gamma> P' (f P'') \<and> (\<Gamma> \<Turnstile> f(P'') - \<alpha> \<rightarrow> (f (P'''))) )
    ) 
    ))"

(* it's also an equivalence relation *)    
    
lemma reflp_iso : "reflp (isomorph \<Gamma>)"
  unfolding reflp_def by fastforce
  
lemma symp_iso : "symp (isomorph \<Gamma>)"
  unfolding symp_def
  by (smt bij_betw_imp_inj_on bij_betw_inv_into inj_image_mem_iff inv_into_f_f range_eqI) (*this might take a while*)
  
lemma symp_trans : "transp (isomorph \<Gamma>)"
  unfolding transp_def
  proof(safe)
  fix x::"process"
  fix f::"process\<Rightarrow>process"
  fix fa::"process\<Rightarrow>process"
  assume 1:"bij f"
  assume 2:"bij fa"
  obtain fb::"process\<Rightarrow>process" where fb:"fb = fa \<circ> f" by blast
  then have bij_fb:"bij fb" using 1 2 by (simp add: bij_comp)
  assume a:"\<forall>P'' P''' \<alpha>. (Reach \<Gamma> x P'' \<and> \<Gamma> \<Turnstile>  P'' - \<alpha> \<rightarrow> P''') = (Reach \<Gamma> (f x) (f P'') \<and> \<Gamma> \<Turnstile>  f P'' - \<alpha> \<rightarrow> f P''')"
  assume b:"\<forall>P'' P''' \<alpha>. (Reach \<Gamma> (f x) P'' \<and> \<Gamma> \<Turnstile>  P'' - \<alpha> \<rightarrow> P''') = (Reach \<Gamma> (fa (f x)) (fa P'') \<and> \<Gamma> \<Turnstile>  fa P'' - \<alpha> \<rightarrow> fa P''')"
  from a b fb have fb_fa_f:"fb x = fa (f x)" by simp
  from a b fb have fb_iso:"(\<forall>P'' P''' \<alpha>. (Reach \<Gamma> x P'' \<and> \<Gamma> \<Turnstile>  P'' - \<alpha> \<rightarrow> P''') = (Reach \<Gamma> (fa (f x)) (fb P'') \<and> \<Gamma> \<Turnstile>  fb P'' - \<alpha> \<rightarrow> fb P'''))" by (metis comp_apply)
  show "\<exists>fb. bij fb \<and>
            fb x = fa (f x) \<and>
            (\<forall>P'' P''' \<alpha>. (Reach \<Gamma> x P'' \<and> \<Gamma> \<Turnstile>  P'' - \<alpha> \<rightarrow> P''') = (Reach \<Gamma> (fa (f x)) (fb P'') \<and> \<Gamma> \<Turnstile>  fb P'' - \<alpha> \<rightarrow> fb P'''))"
  using bij_fb fb_fa_f fb_iso by blast
qed

(* We have two equalities, so let's compare them *)

(* helper lemma, which is unfortunately not proven yet *)
lemma h: assumes iso:"isomorph \<Gamma> P P'" 
      shows "TraceHelper \<Gamma> P Q trace \<Longrightarrow> \<exists> Q'. TraceHelper \<Gamma> P' Q' trace \<and> isomorph \<Gamma> Q Q'" using iso
      proof(induction trace arbitrary: P)
      case(Nil) then show "?case" by (metis Nil_is_append_conv TraceHelper.cases base not_Cons_self)
      next
      case(Cons t trace)
      then show "?case"
      apply(auto)
      apply(rule)
      apply(rule)
      apply(auto)
      sorry (* probably requires an induction which appends at the end of trace *)
qed

lemma iso_in_tr_strict: "isomorph \<Gamma> P P' \<Longrightarrow> trace_equiv \<Gamma> P P'" 
proof(-)
  assume iso:"isomorph \<Gamma> P P'"
   show "\<forall>traces. Traces \<Gamma> P traces = Traces \<Gamma> P' traces" proof
    fix trace
    have osi:"isomorph \<Gamma> P' P" using symp_iso iso by (smt bij_betw_inv_into bij_is_surj inv_inv_eq surj_f_inv_f) 
    show "Traces \<Gamma> P trace = Traces \<Gamma> P' trace" proof
      assume "Traces \<Gamma> P trace"
      then have "\<exists> Q. TraceHelper \<Gamma> P Q trace"  using Traces.cases by blast
      then obtain Q::process where 1:"TraceHelper \<Gamma> P Q trace" by blast
      then have " \<exists> Q'. TraceHelper \<Gamma> P' Q' trace \<and> isomorph \<Gamma> Q Q'" using iso h by presburger
      then obtain Q'::process where 2:"TraceHelper \<Gamma> P' Q' trace \<and> isomorph \<Gamma> Q Q'" by blast
      from 2 have "TraceHelper \<Gamma> P' Q' trace" by simp
      then show "Traces \<Gamma> P' trace" by blast
      next
      assume "Traces \<Gamma> P' trace"
      then have "\<exists> Q. TraceHelper \<Gamma> P' Q trace"  using Traces.cases by blast
      then obtain Q::process where 1:"TraceHelper \<Gamma> P' Q trace" by blast
      then have " \<exists> Q'. TraceHelper \<Gamma> P Q' trace \<and> isomorph \<Gamma> Q Q'" using osi h by presburger
      then obtain Q'::process where 2:"TraceHelper \<Gamma> P Q' trace \<and> isomorph \<Gamma> Q Q'" by blast
      from 2 have "TraceHelper \<Gamma> P Q' trace" by simp
      then show "Traces \<Gamma> P trace" by blast
    qed
  qed
qed


(* The next step would be to prove that the inclusion is strict
  e.g. using the counterexample below.
  However, the proof was skipped due to time constraints
  To prove the trace equivalence and to disprove the isomorphy I wanted to use a function instead of
  an inductive predicate, in the hope that it would facilliate the proof
  -- unfortunately the function turned out not only to be not complete (as expected), but was also not sound 
  
  NOT_WORKING
fun collect_outgoing_transitions :: "env \<Rightarrow> process \<Rightarrow> nat \<Rightarrow> transition_relation" where
"collect_outgoing_transitions \<Gamma> P  0 = {}" |
"collect_outgoing_transitions \<Gamma> Stop _ = {}" |
"collect_outgoing_transitions \<Gamma> (a \<cdot> X) _ = { (a \<cdot> X , a, X)  } " |
"collect_outgoing_transitions \<Gamma> (X +ccs Y) depth =
  { (X +ccs Y, \<alpha>, P') |  \<alpha> P' P.  (P, \<alpha>, P') \<in> ((collect_outgoing_transitions \<Gamma> X depth)\<union>
                                                 (collect_outgoing_transitions \<Gamma> Y depth)) }" |
"collect_outgoing_transitions \<Gamma> (X \<bar> Y) depth = 
  { (X \<bar> Y, \<alpha>, P' \<bar> Y) |  \<alpha> P'.  (X, \<alpha>, P') \<in> (collect_outgoing_transitions \<Gamma> X depth)} \<union>
  { (X \<bar> Y, \<alpha>,  X \<bar> P') |  \<alpha> P'.  (Y, \<alpha>, P') \<in> (collect_outgoing_transitions \<Gamma> Y depth)} \<union>
  { (X \<bar> Y, \<tau>, X' \<bar> Y') |  a X' Y'.  (X, a, X') \<in> (collect_outgoing_transitions \<Gamma> X depth) \<and> 
                                     (Y, compl a, Y') \<in> (collect_outgoing_transitions \<Gamma> Y depth)}" |
"collect_outgoing_transitions \<Gamma> (P \<setminus> H) depth = {(P \<setminus> H, \<alpha>, P' \<setminus> H) | P' \<alpha>.   (P, \<alpha>, P') \<in> (collect_outgoing_transitions \<Gamma> P depth) \<and> \<not> (restricted \<alpha> H)} " | 
(* recursion is broken: needs to adjust result *)
"collect_outgoing_transitions \<Gamma> (Rec X) depth = (case (\<Gamma> X) of Some P \<Rightarrow>  collect_outgoing_transitions \<Gamma> P (depth - 1)
                                                       | None \<Rightarrow> {} )"

lemma "(P, \<alpha>, P') \<in> collect_outgoing_transitions \<Gamma> (X \<bar> Y) depth \<Longrightarrow> depth > 0 \<and> (
  (P' = X' \<bar> Y \<and>  (X, \<alpha>, X') \<in> collect_outgoing_transitions \<Gamma> X depth) \<or>
  (P' = X' \<bar> Y \<and>  (Y, \<alpha>, Y') \<in> collect_outgoing_transitions \<Gamma> X depth) \<or>
  ( P' = X' \<bar> Y'  \<and> \<alpha> = \<tau>  \<and> (\<exists> a.
   (X, a, X') \<in> collect_outgoing_transitions \<Gamma> X depth \<and>
   (Y, compl a, Y') \<in> collect_outgoing_transitions \<Gamma> X depth))
)"
nitpick


lemma transitions_sound: "(Q, \<alpha>, Q') \<in>  collect_outgoing_transitions \<Gamma> P n \<Longrightarrow> \<Gamma> \<Turnstile> Q - \<alpha> \<rightarrow> Q'"
apply(induction P)
apply (metis collect_outgoing_transitions.simps(1) collect_outgoing_transitions.simps(2) empty_iff old.nat.exhaust)
apply (metis (no_types, hide_lams) collect_outgoing_transitions.simps(1) collect_outgoing_transitions.simps(3) empty_iff insert_iff not0_implies_Suc old.prod.inject prefix)
oops
*)

lemma "trace_equiv \<Gamma> ( !''a'' \<cdot> ((!''b'' \<cdot> Stop) +ccs (!''c'' \<cdot> Stop)) )
                     (( !''a'' \<cdot> !''b'' \<cdot> Stop) +ccs ( !''a'' \<cdot> !''c'' \<cdot> Stop) )"
oops


lemma "\<not> isomorph \<Gamma> ( !''a'' \<cdot> ((!''b'' \<cdot> Stop) +ccs (!''c'' \<cdot> Stop)) )
                     (( !''a'' \<cdot> !''b'' \<cdot> Stop) +ccs ( !''a'' \<cdot> !''c'' \<cdot> Stop) )"
oops



(* new equality: strong bisimilarity *)

(* first we describe what a strong bisimulation is (Definition 17 in the book) *)
abbreviation is_strong_bisimulation :: "env \<Rightarrow>(process \<times> process) set \<Rightarrow> bool" where
  "is_strong_bisimulation \<Gamma> R \<equiv>
   (\<forall> (s,t) \<in> R. \<forall> (\<alpha>::action). \<forall> s'.  (\<Gamma> \<Turnstile> s -\<alpha> \<rightarrow> s') \<longrightarrow> (\<exists> t'. (\<Gamma> \<Turnstile> t - \<alpha> \<rightarrow> t') \<and> (s',t') \<in> R  )) \<and>
   (\<forall> (s,t) \<in> R. \<forall> (\<alpha>::action). \<forall> t'.  (\<Gamma> \<Turnstile> t -\<alpha> \<rightarrow> t') \<longrightarrow> (\<exists> s'. (\<Gamma> \<Turnstile> s - \<alpha> \<rightarrow> s') \<and> (s',t') \<in> R  ))"

(* and then what bisimilar means *)
abbreviation strong_bisim :: "env \<Rightarrow> process \<Rightarrow> process \<Rightarrow> bool" where
  "strong_bisim \<Gamma> P P' \<equiv>
  (
    \<exists> (R:: (process \<times> process) set). (
         (P, P') \<in> R \<and>
         is_strong_bisimulation \<Gamma> R
    )
  )
  "
  
(* let's show again that it's actually an equivalence relation *)

lemma reflp_strong_bisim: "reflp (strong_bisim \<Gamma>)"
unfolding reflp_def by blast

lemma symp_strong_bisim: "symp (strong_bisim \<Gamma>)"
unfolding symp_def proof(safe)
  fix x::process
  fix y::process
  fix R
  assume 0:"(x, y) \<in> R"
  assume 1:"\<forall>(s, t)\<in>R. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> R)"
  assume 2:"\<forall>(s, t)\<in>R. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> R)"
  show "strong_bisim \<Gamma> y x" proof
    let ?R = "converse R"
    have "(y, x) \<in> ?R" using 0 by simp
    moreover have "\<forall>(s, t)\<in>?R. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> ?R)" using 2 by fast
    moreover have "\<forall>(s, t)\<in>?R. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> ?R)" using 1 by fast
    ultimately show "(y, x) \<in> ?R \<and>
    (\<forall>(s, t)\<in>?R. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> ?R)) \<and>
    (\<forall>(s, t)\<in>?R. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> ?R))" by simp
  qed
qed

lemma transp_strong_bisim: "transp (strong_bisim \<Gamma>)"
unfolding transp_def proof(safe)
  fix x::process
  fix y::process
  fix z::process
  fix R Ra
  assume 0:"(x, y) \<in> R"
  assume 1:"\<forall>(s, t)\<in>R. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> R)"
  assume 2:"\<forall>(s, t)\<in>R. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> R)"
  assume a:"(y, z) \<in> Ra"
  assume b:"\<forall>(s, t)\<in>Ra. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> Ra)"
  assume c:"\<forall>(s, t)\<in>Ra. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> Ra)"
  show "strong_bisim \<Gamma> x z" proof
    let ?R = "R O Ra"
    have "(x,z) \<in> ?R" using 0 a by blast
    moreover have "(\<forall>(s, t)\<in>?R. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> ?R))" using 1 b by fast
    moreover have "(\<forall>(s, t)\<in>?R. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> ?R))" using 2 c by fast
    ultimately show "(x, z) \<in> ?R \<and>
    (\<forall>(s, t)\<in>?R. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> ?R)) \<and>
    (\<forall>(s, t)\<in>?R. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> ?R))" by simp
  qed
qed

(* Lemma 2 in the book shows a different way to obtain bisimilarity
  We show later that definition and lemma agree
*)
abbreviation bisimilarity :: "env \<Rightarrow> (process \<times> process) set" where
  "bisimilarity \<Gamma> \<equiv> (\<Union> { R . is_strong_bisimulation \<Gamma> R } )"
  
(* bisimilarity is the largest bisimulation (shown in two lemmas *)

lemma bisimilarity_is_a_strong_bisimulation: "is_strong_bisimulation \<Gamma> (bisimilarity \<Gamma>)"
proof
  show "\<forall>(s, t)\<in>bisimilarity \<Gamma>. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma>)"
  proof
  fix x
  assume "x \<in> bisimilarity \<Gamma>"
  then have "\<exists> R. is_strong_bisimulation \<Gamma> R \<and> x \<in> R" by (metis (mono_tags, lifting) CollectD UnionE)
  then obtain R where 1:"is_strong_bisimulation \<Gamma> R \<and> x \<in> R" by blast
  then have "is_strong_bisimulation \<Gamma> R" by blast
  from 1 have 2:"case x of (s, t) \<Rightarrow> \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> R)"  by fast 
  have 3:"\<And> a b. (a,b) \<in> R \<Longrightarrow> (a,b) \<in> bisimilarity \<Gamma>"  using `is_strong_bisimulation \<Gamma> R` by blast
  show "case x of (s, t) \<Rightarrow> \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> (bisimilarity \<Gamma>))" using 2 3
  by (smt Pair_inject case_prodE split_cong) (*takes some time*)
  qed
  show "\<forall>(s, t)\<in>bisimilarity \<Gamma>. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma>)"
  proof
  fix x
  assume "x \<in> bisimilarity \<Gamma>"
  then have "\<exists> R. is_strong_bisimulation \<Gamma> R \<and> x \<in> R" by (metis (mono_tags, lifting) CollectD UnionE)
  then obtain R where 1:"is_strong_bisimulation \<Gamma> R \<and> x \<in> R" by blast
  then have "is_strong_bisimulation \<Gamma> R" by blast
  from 1 have 2:"case x of (s, t) \<Rightarrow> \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> R)" by fast
  have 3:"\<And> a b. (a,b) \<in> R \<Longrightarrow> (a,b) \<in> bisimilarity \<Gamma>"  using `is_strong_bisimulation \<Gamma> R` by blast
  show "case x of (s, t) \<Rightarrow> \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma>)" using 2 3
  by (smt Pair_inject case_prodE split_cong) (*takes some time*)
  qed
qed

lemma bisimilarity_is_the_largest_bisimulation:
assumes 0:"is_strong_bisimulation \<Gamma> R"
assumes 1:"bisimilarity \<Gamma> \<subseteq> R"
shows "R = bisimilarity \<Gamma>" using 0 1
by(auto)

(* As it could help later, we show that bisimilarity is an equivalence also for the other definition *)
lemma refl_bisimilarity: "refl (bisimilarity \<Gamma>)"
unfolding refl_on_def proof
  show "bisimilarity \<Gamma> \<subseteq> UNIV \<times> UNIV" by fast
  show "\<forall>x\<in>UNIV. (x, x) \<in> bisimilarity \<Gamma>" by force
qed

lemma sym_bisimilarity: "sym (bisimilarity \<Gamma>)"
unfolding sym_def proof
  fix x
  show " \<forall>y. (x, y) \<in> bisimilarity \<Gamma> \<longrightarrow> (y, x) \<in> bisimilarity \<Gamma>" proof
  fix y
  show "(x, y) \<in> bisimilarity \<Gamma> \<longrightarrow> (y, x) \<in> bisimilarity \<Gamma>" proof
  assume "(x,y) \<in> bisimilarity \<Gamma>"
  then have "\<exists> R. is_strong_bisimulation \<Gamma> R \<and> (x,y) \<in> R" by (metis (mono_tags, lifting) CollectD UnionE)
  then obtain R where 1:"is_strong_bisimulation \<Gamma> R \<and> (x,y) \<in> R" by blast
  then have 0:"(x,y) \<in> R" by blast
  from 1 have "is_strong_bisimulation \<Gamma> R" by blast
  then have "is_strong_bisimulation \<Gamma> (R \<inverse>)" using symp_strong_bisim by fast
  then have 2:"(R \<inverse>) \<subseteq> bisimilarity \<Gamma>" by blast
  have "(y,x) \<in> (R \<inverse>)" using 0 by simp 
  then show "(y,x) \<in> bisimilarity \<Gamma>" using 2 by blast
  qed
  qed
qed

lemma trans_bisimilarity: "trans (bisimilarity \<Gamma>)"
unfolding trans_def proof
fix x
show "\<forall>y z. (x, y) \<in> bisimilarity \<Gamma> \<longrightarrow> (y, z) \<in> bisimilarity \<Gamma> \<longrightarrow> (x, z) \<in> bisimilarity \<Gamma>" proof
fix y
show "\<forall> z. (x, y) \<in> bisimilarity \<Gamma> \<longrightarrow> (y, z) \<in> bisimilarity \<Gamma> \<longrightarrow> (x, z) \<in> bisimilarity \<Gamma>" proof
fix z
show "(x, y) \<in> bisimilarity \<Gamma> \<longrightarrow> (y, z) \<in> bisimilarity \<Gamma> \<longrightarrow> (x, z) \<in> bisimilarity \<Gamma>" proof
show "(x, y) \<in> bisimilarity \<Gamma> \<Longrightarrow> (y, z) \<in> bisimilarity \<Gamma> \<longrightarrow> (x, z) \<in> bisimilarity \<Gamma>" proof
  assume "(x, y) \<in> bisimilarity \<Gamma>"
  then have "\<exists> R1. is_strong_bisimulation \<Gamma> R1 \<and> (x,y) \<in> R1" by (metis (mono_tags, lifting) CollectD UnionE)
  then obtain R1 where 0:"is_strong_bisimulation \<Gamma> R1 \<and> (x,y) \<in> R1" by blast
  from 0 have 00:"is_strong_bisimulation \<Gamma> R1" by blast
  from 0 have 01:"(x,y) \<in> R1" by blast 

  assume "(y, z) \<in> bisimilarity \<Gamma>"
  then have "\<exists> R2. is_strong_bisimulation \<Gamma> R2 \<and> (y,z) \<in> R2" by (metis (mono_tags, lifting) CollectD UnionE)
  then obtain R2 where 1:"is_strong_bisimulation \<Gamma> R2 \<and> (y,z) \<in> R2" by blast
  from 1 have 10:"is_strong_bisimulation \<Gamma> R2" by blast
  from 1 have 11:"(y,z) \<in> R2" by blast
  
  have "is_strong_bisimulation \<Gamma> (R1 O R2)" using 00 10 transp_strong_bisim by fast
  then have 20:"(R1 O R2) \<subseteq> bisimilarity \<Gamma>" by blast
  have 21:"(x,z) \<in> (R1 O R2)" using 01 11 by blast
  
  show "(x, z) \<in> bisimilarity \<Gamma>" using 20 21 by blast
  qed qed qed qed
qed

lemma bisimilarity_is_indeed_bisimilarity: "(P,Q) \<in> bisimilarity \<Gamma> \<longleftrightarrow> strong_bisim \<Gamma> P Q"
by(auto)

(* Bisimilarity is not only an equivalence, but even a congruence (for all CCS operators).
   We show proofs for prefix and choice *)

(* showing the congruence property for prefix is as easy as those proofs get *)
lemma strong_bisim_prefix: 
assumes orig:"(P,Q) \<in> bisimilarity \<Gamma>"
shows " ((\<alpha> \<cdot> P), (\<alpha> \<cdot> Q)) \<in> bisimilarity \<Gamma>" proof
  let ?X = " (bisimilarity \<Gamma>) \<union>  { ((\<alpha> \<cdot> P), (\<alpha> \<cdot> Q)) }"
  show "(\<alpha> \<cdot> P, \<alpha> \<cdot> Q) \<in> ?X" by blast
  show "bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)} \<in> {R. is_strong_bisimulation \<Gamma> R}" proof
  show "is_strong_bisimulation \<Gamma> (bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)})" proof
  show "\<forall>(s, t)\<in>bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)}. \<forall>\<alpha>' s'. \<Gamma> \<Turnstile>  s - \<alpha>' \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha>' \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)})"
  proof(safe)
    fix a b \<alpha>' s'
    assume "\<Gamma> \<Turnstile>  \<alpha> \<cdot> P - \<alpha>' \<rightarrow> s'"
    then have 0:"s' = P \<and> \<alpha>' = \<alpha>" proof(auto)
      assume " \<Gamma> \<Turnstile>  \<alpha> \<cdot> P - \<alpha>' \<rightarrow> s'"
      then show "s' = P" by(rule;safe)
      next
      assume "\<Gamma> \<Turnstile>  \<alpha> \<cdot> P - \<alpha>' \<rightarrow> s'"
      then show "\<alpha>' = \<alpha>" by(rule;safe)
    qed
    then have 1:"\<Gamma> \<Turnstile>  \<alpha> \<cdot> P - \<alpha> \<rightarrow> P" by blast
    have "\<Gamma> \<Turnstile>  \<alpha> \<cdot> Q - \<alpha> \<rightarrow> Q" by auto
    then show "\<exists>t'. \<Gamma> \<Turnstile>  \<alpha> \<cdot> Q - \<alpha>' \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)}" using 0 1 using orig by blast
  next
    fix a::process
    fix b::process
    fix \<alpha>' s' X
    assume c:"(a, b) \<in> X"
    assume a:" \<forall>(s, t)\<in>X. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> X)"
    assume b:"\<forall>(s, t)\<in>X. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> X)"
    from a b have "is_strong_bisimulation \<Gamma> X" by blast
    then have d:"X \<subseteq> bisimilarity \<Gamma>" by blast
    
    assume "\<Gamma> \<Turnstile>  a - \<alpha>' \<rightarrow> s'"
    then have "\<exists> t'. \<Gamma> \<Turnstile> b - \<alpha>' \<rightarrow> t' \<and> (s', t') \<in> X" using a c by blast
    then obtain t' where "\<Gamma> \<Turnstile> b - \<alpha>' \<rightarrow> t'  \<and> (s', t') \<in> X " by blast 
    show "\<exists>t'. \<Gamma> \<Turnstile>  b - \<alpha>' \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)}" using d by (meson `\<Gamma> \<Turnstile> b - \<alpha>' \<rightarrow> t' \<and> (s', t') \<in> X` subsetCE sup_ge1)
 qed
 show "\<forall>(s, t)\<in>bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)}. \<forall>\<alpha>' t'. \<Gamma> \<Turnstile>  t - \<alpha>' \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha>' \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)})"
 proof(safe)
   fix a b \<alpha>' t'
   assume "\<Gamma> \<Turnstile>  \<alpha> \<cdot> Q - \<alpha>' \<rightarrow> t'"
    then have 0:"t' = Q \<and> \<alpha>' = \<alpha>" proof(auto)
      assume " \<Gamma> \<Turnstile>  \<alpha> \<cdot> Q - \<alpha>' \<rightarrow> t'"
      then show "t' = Q" by(rule;safe)
      next
      assume "\<Gamma> \<Turnstile>  \<alpha> \<cdot> Q - \<alpha>' \<rightarrow> t'"
      then show "\<alpha>' = \<alpha>" by(rule;safe)
    qed
    then have 1:"\<Gamma> \<Turnstile>  \<alpha> \<cdot> Q - \<alpha> \<rightarrow> Q" by blast
    have "\<Gamma> \<Turnstile>  \<alpha> \<cdot> P - \<alpha> \<rightarrow> P" by auto
   then show "\<exists>s'. \<Gamma> \<Turnstile>  \<alpha> \<cdot> P - \<alpha>' \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)}" using 0 1 using orig by blast
 next
   fix a::process
   fix b::process
   fix \<alpha>' t' X
   assume c:"(a, b) \<in> X"
   assume a:"\<forall>(s, t)\<in>X. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> X)"
   assume b:"\<forall>(s, t)\<in>X. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> X)"
   from a b have "is_strong_bisimulation \<Gamma> X" by blast
   then have d:"X \<subseteq> bisimilarity \<Gamma>" by blast
   
   assume "\<Gamma> \<Turnstile>  b - \<alpha>' \<rightarrow> t'"
   then have "\<exists>s'. \<Gamma> \<Turnstile>  a - \<alpha>' \<rightarrow> s' \<and> (s', t') \<in> X" using b c by blast
   then obtain s' where "\<Gamma> \<Turnstile>  a - \<alpha>' \<rightarrow> s' \<and> (s', t') \<in> X" by blast
   then show "\<exists>s'. \<Gamma> \<Turnstile>  a - \<alpha>' \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(\<alpha> \<cdot> P, \<alpha> \<cdot> Q)}" by (metis (no_types, lifting) d subsetCE sup_ge1)
 qed
qed qed qed


(* showing the congruence property for choice is not hard, but even more annoying than prefix
 * showing that this property does also hold when the process is attached on the right side
 * is left as an exercise for the reader
 *)
lemma strong_bisim_cong_choice_left: 
assumes orig:"(P,Q) \<in> bisimilarity \<Gamma>"
shows " ((N +ccs P), (N +ccs Q)) \<in> bisimilarity \<Gamma>" proof
  let ?X = "(bisimilarity \<Gamma>)   \<union>   {((N +ccs P), (N +ccs Q))} "
  show "(N +ccs P, N +ccs Q) \<in> ?X" by blast
  show "bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)} \<in> {R. is_strong_bisimulation \<Gamma> R}" proof
    show "is_strong_bisimulation \<Gamma> (bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)})" proof
    show "\<forall>(s, t)\<in>bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)})"
    proof(safe)
        fix a b \<alpha> s'
        assume "\<Gamma> \<Turnstile>  N - \<alpha> \<rightarrow> s'"
        then have 1:"\<Gamma> \<Turnstile> N +ccs Q - \<alpha> \<rightarrow> s'" by blast
        then have "(s', s') \<in> bisimilarity \<Gamma>" using  UNIV_I refl_bisimilarity refl_on_def
        proof -
          have "\<And>p f. p \<notin> UNIV \<or> (p, p) \<in> \<Union>{r. (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> p - a \<rightarrow> paa \<longrightarrow> (\<exists>p. f \<Turnstile> pa - a \<rightarrow> p \<and> (paa, p) \<in> r))) \<and> (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> pa - a \<rightarrow> paa \<longrightarrow> (\<exists>pa. f \<Turnstile> p - a \<rightarrow> pa \<and> (pa, paa) \<in> r)))}"
            using refl_bisimilarity refl_on_def ext
            proof -
              fix p :: process and f :: "char list \<Rightarrow> process option"
              have "refl (\<Union>{r. (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> p - a \<rightarrow> paa \<longrightarrow> (\<exists>p. f \<Turnstile> pa - a \<rightarrow> p \<and> (paa, p) \<in> r))) \<and> (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> pa - a \<rightarrow> paa \<longrightarrow> (\<exists>pa. f \<Turnstile> p - a \<rightarrow> pa \<and> (pa, paa) \<in> r)))})"
                by (metis refl_bisimilarity)
              thus "p \<notin> UNIV \<or> (p, p) \<in> \<Union>{r. (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> p - a \<rightarrow> paa \<longrightarrow> (\<exists>p. f \<Turnstile> pa - a \<rightarrow> p \<and> (paa, p) \<in> r))) \<and> (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> pa - a \<rightarrow> paa \<longrightarrow> (\<exists>pa. f \<Turnstile> p - a \<rightarrow> pa \<and> (pa, paa) \<in> r)))}"
                by (meson refl_on_def)
            qed (* this proof was sponsored by  SPASS + proof reconstruction -- metis is too slow *)
              thus ?thesis
                by (meson UNIV_I)
            qed 
        then show "\<exists>t'. \<Gamma> \<Turnstile>  N +ccs Q - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}" using 1 by blast
      next
        fix a b \<alpha> s'
        from orig have "strong_bisim \<Gamma> P Q" using bisimilarity_is_indeed_bisimilarity by blast
        then obtain R where 0:" (P, Q) \<in> R \<and> is_strong_bisimulation \<Gamma> R" by blast
        then have "is_strong_bisimulation \<Gamma> R" by blast
        then have 1:"R \<subseteq> bisimilarity \<Gamma>" by blast
        assume "\<Gamma> \<Turnstile>  P - \<alpha> \<rightarrow> s'"
        then have "\<exists>t'. \<Gamma> \<Turnstile>  Q - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> R" using 0 by blast
        then obtain t' where "\<Gamma> \<Turnstile>  Q - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> R" by blast
        then have "\<Gamma> \<Turnstile>  (N +ccs Q) - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> R" by blast
        then show "\<exists>t'. \<Gamma> \<Turnstile>  N +ccs Q - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}" using 1 by (meson UnCI subsetCE)
      next
       fix a::process
       fix b::process 
       fix \<alpha> s' X
       assume c:"(a, b) \<in> X"
       assume a:"\<forall>(s, t)\<in>X. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> X)"
       assume b:"\<forall>(s, t)\<in>X. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> X)"
       have "is_strong_bisimulation \<Gamma> X" using a b by blast
       then have d:"X \<subseteq> bisimilarity \<Gamma>" by blast
       assume "\<Gamma> \<Turnstile>  a - \<alpha> \<rightarrow> s'"
       then have "\<exists> t'. \<Gamma> \<Turnstile> b - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> X" using a c by fast
       then obtain t' where "\<Gamma> \<Turnstile> b - \<alpha> \<rightarrow> t'  \<and> (s', t') \<in> X " by blast 
       then show "\<exists>t'. \<Gamma> \<Turnstile>  b - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}" using d  by (meson UnCI subsetCE)
     qed
     (* and again *)
     show "\<forall>(s, t)\<in>bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)})"
     proof(safe)
        fix a b \<alpha> t'
        assume "\<Gamma> \<Turnstile>  N - \<alpha> \<rightarrow> t'"
        then have 1:"\<Gamma> \<Turnstile> N +ccs P - \<alpha> \<rightarrow> t'" by blast
        then have "(t', t') \<in> bisimilarity \<Gamma>" using  UNIV_I refl_bisimilarity refl_on_def
        proof -
          have "\<And>p f. p \<notin> UNIV \<or> (p, p) \<in> \<Union>{r. (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> p - a \<rightarrow> paa \<longrightarrow> (\<exists>p. f \<Turnstile> pa - a \<rightarrow> p \<and> (paa, p) \<in> r))) \<and> (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> pa - a \<rightarrow> paa \<longrightarrow> (\<exists>pa. f \<Turnstile> p - a \<rightarrow> pa \<and> (pa, paa) \<in> r)))}"
            using refl_bisimilarity refl_on_def ext
            proof -
              fix p :: process and f :: "char list \<Rightarrow> process option"
              have "refl (\<Union>{r. (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> p - a \<rightarrow> paa \<longrightarrow> (\<exists>p. f \<Turnstile> pa - a \<rightarrow> p \<and> (paa, p) \<in> r))) \<and> (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> pa - a \<rightarrow> paa \<longrightarrow> (\<exists>pa. f \<Turnstile> p - a \<rightarrow> pa \<and> (pa, paa) \<in> r)))})"
                by (metis refl_bisimilarity)
              thus "p \<notin> UNIV \<or> (p, p) \<in> \<Union>{r. (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> p - a \<rightarrow> paa \<longrightarrow> (\<exists>p. f \<Turnstile> pa - a \<rightarrow> p \<and> (paa, p) \<in> r))) \<and> (\<forall>p. p \<in> r \<longrightarrow> (case p of (p, pa) \<Rightarrow> \<forall>a paa. f \<Turnstile> pa - a \<rightarrow> paa \<longrightarrow> (\<exists>pa. f \<Turnstile> p - a \<rightarrow> pa \<and> (pa, paa) \<in> r)))}"
                by (meson refl_on_def)
            qed (* this proof was sponsored by  SPASS + proof reconstruction -- metis is too slow *)
              thus ?thesis
                by (meson UNIV_I)
            qed 
        then show "\<exists>s'. \<Gamma> \<Turnstile>  N +ccs P - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}" using 1 by blast
      next
        fix a b \<alpha> t'
        from orig have "strong_bisim \<Gamma> P Q" using bisimilarity_is_indeed_bisimilarity by blast
        then obtain R where 0:" (P, Q) \<in> R \<and> is_strong_bisimulation \<Gamma> R" by blast
        then have "is_strong_bisimulation \<Gamma> R" by blast
        then have 1:"R \<subseteq> bisimilarity \<Gamma>" by blast
        assume "\<Gamma> \<Turnstile>  Q - \<alpha> \<rightarrow> t'"
        then have "\<exists>s'. \<Gamma> \<Turnstile>  P - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> R" using 0 by blast
        then obtain s' where "\<Gamma> \<Turnstile>  P - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> R" by blast
        then have "\<Gamma> \<Turnstile>  (N +ccs P) - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> R" by blast
        then show "\<exists>s'. \<Gamma> \<Turnstile>  N +ccs P - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}"  using 1 by (meson UnCI subsetCE)
      next
       fix a::process
       fix b::process
       fix \<alpha> t' X
       assume c:"(a, b) \<in> X"
       assume a:"\<forall>(s, t)\<in>X. \<forall>\<alpha> s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<longrightarrow> (\<exists>t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<and> (s', t') \<in> X)"
       assume b:"\<forall>(s, t)\<in>X. \<forall>\<alpha> t'. \<Gamma> \<Turnstile>  t - \<alpha> \<rightarrow> t' \<longrightarrow> (\<exists>s'. \<Gamma> \<Turnstile>  s - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> X)"
       have "is_strong_bisimulation \<Gamma> X" using a b by blast
       then have d:"X \<subseteq> bisimilarity \<Gamma>" by blast
       assume "\<Gamma> \<Turnstile>  b - \<alpha> \<rightarrow> t'"
       then have "\<exists> s'. \<Gamma> \<Turnstile> a - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> X" using b c by fast
       then obtain s' where " \<Gamma> \<Turnstile> a - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> X"  by blast 
       show "\<exists>s'. \<Gamma> \<Turnstile>  a - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> bisimilarity \<Gamma> \<union> {(N +ccs P, N +ccs Q)}"  using d by (meson UnCI `\<Gamma> \<Turnstile> a - \<alpha> \<rightarrow> s' \<and> (s', t') \<in> X` subsetCE)  
     qed
    qed
  qed
qed


end
