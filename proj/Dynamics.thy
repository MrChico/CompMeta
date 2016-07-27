theory Dynamics
imports RhoCalc NameEquiv Substitution
begin

section\<open>Operational Semantics\<close>
text\<open>The following processes gives a set of reduction rules which corresponds to the dynamics
of the rho-calculus. Essentially, the main way in which a process can reduce is by synchronization:
If two processes P and Q run in parallel, where P is listening on a channel (name equivalent to) y,
and Q is ready to output a process R on the channel y, then P and Q will synchronize.
The name to which P writes the input will be substituted throughout the rest of P to 'R'.
This reduction is called the communication rule:
\begin{equation}
\infer[COMM]{x_0 \triangleleft Q \triangleright | x_1(y).P \rightarrow P{'Q' \setminus y}}{x_0 \equiv_N x_1}
\end{equation}
\<close>
fun toPar:: "P list \<Rightarrow> P" where
  "toPar []   = Null"
 |"toPar (x#[]) = x"
 |"toPar (x#y#xs) = (x \<parallel> (toPar (y#xs)))"



fun syncable:: "P \<Rightarrow> P \<Rightarrow> bool" where
  "syncable (Lift x Q) (Input y z P)    = (x =N z)"
 |"syncable (Input y z P) (Lift x Q)    = (x =N z)"
 |"syncable (Lift y P) (Lift x Q)       = False"
 |"syncable (Input y z P) (Input a b Q) = False"
 |"syncable _ (vc \<parallel> vd)                 = False"
 |"syncable   (vc \<parallel> vd) _               = False"
 |"syncable   (\<acute>v`) _                   = False"
 |"syncable _ (\<acute>v`)                     = False"
 |"syncable   Null _                    = False"
 |"syncable _ Null                      = False"

fun sync:: "P \<Rightarrow> P \<Rightarrow> P" where
  "sync (Lift x Q) (Input y z P) = (P s{`Q\<acute>\<setminus>y})"
 |"sync (Input y z P) (Lift x Q) = (P s{`Q\<acute>\<setminus>y})"

function fineRun:: "P list \<Rightarrow> P list \<Rightarrow> P list \<Rightarrow> P list" where
   "fineRun []     []  []         = []"
  |"fineRun (x#[]) []  []         = (x#[])"
  |"fineRun (x#y#xs) []  zs       = (fineRun (y#xs) (x#[]) zs)"
  |"fineRun [] (y#ys) (z#[])      = (z#y#ys)"
  |"fineRun [] (y#ys) (z#zs)      = (fineRun zs (z#y#ys) [])"
  |"fineRun (x#xs) (y#ys) zs      = (if (syncable x y) then ((sync x y)#xs@ys@zs) else (fineRun (xs) (y#ys) (x#zs)))"
apply auto
sorry
termination
sorry

fun step:: "P \<Rightarrow> P" where
  "step P = toPar( fineRun (getList P) [] [])"

subsection\<open>Example: replication\<close>
text\<open>In traditional process calculae, there is usually a specific construction for \<close>
abbreviation replication where "replication \<equiv> (\<lambda>y.\<lambda>(P,x).(x\<triangleleft>((y\<leftarrow>x.(x[[y]]\<parallel>\<acute>y`).)\<parallel>P)\<triangleright>\<parallel>(y \<leftarrow> x.(x[[y]]\<parallel>\<acute>y`).)))(`zero[[zero]]\<acute>)"
abbreviation xx where "xx \<equiv> zero"
abbreviation yy where "yy \<equiv> `xx[[xx]]\<acute>"

value "(replication (Two, zero))"
value "step (replication (Two, zero))"
value "step(step (replication (Two, zero)))"
value "step(step(step (replication (Two, zero))))"
value "step(step(step(step (replication (Two, zero)))))"

end
