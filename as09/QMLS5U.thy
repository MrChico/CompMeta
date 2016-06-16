(* Christoph BenzmÃ\<onequarter>ller, February 2016 *)

theory QMLS5U
imports Main

begin


section {* Preliminaris *}

text {*
We present a semantic embedding of quantified modal logic (QML) in classical higher-order logic (HOL). 
Quantifiers are provided for Boolean, first-, second- and 
higher-order variables (for all types).
The theoretical background of the work presented here has been discussed in \cite{J23}. 
This file is intended for reuse by further AFP articles on QML.

We begin by introducing type $i$ for the set of possible worlds and type $\mu$ for the set
of individuals. Formulae in quantified modal logic (QML) are functions from the set of possible worlds
to Booleans. For convenience, their type is written as $\sigma$. *}

typedecl i -- "type for possible worlds" 
typedecl \<mu> -- "type for individuals"      
type_synonym \<sigma> = "(i\<Rightarrow>bool)"

section {* Embedding of Base Logic \emph{K} *}

text {* In Kripke semantics, a modal formula is interpreted over an arbitrary accessibility relation, a
binary relation between possible worlds. *}

consts r :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)    -- "accessibility relation r"   

text {*
The set of classical connectives and quantifiers is \emph{lifted} to the modal level by passing an
additional parameter $w$, representing the current world, to the connectives'
subformulae or binders' scope. This parameter is only used actively in the definition of both
modalities $\{\Box, \diamond\}$, where it is applied to the accessibility relation $r$.

Modal connectives are typeset in bold font.\footnote{In Isabelle/jEdit, bold characters can be
entered by typing \texttt{\textbackslash bol} before entering the actual character.} Abbreviations
are used in place of definitions to avoid explicit mention of the embeddings' definitions when
invoking automated tools via \emph{Sledgehammer}. *}


abbreviation mtrue  :: "\<sigma>" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation mfalse :: "\<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation mnot   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation mnegpred :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>(\<mu>\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53) 
  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi>(x)(w)"   
abbreviation mand   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation mor    :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50)
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation mimp   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation mequ   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  
abbreviation mforall   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")      
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
abbreviation mforallB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9)
  where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
abbreviation mexists   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
abbreviation mexistsB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
abbreviation meq    :: "\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>" (infixr"\<^bold>="52) -- "Equality"  
  where "x\<^bold>=y \<equiv> \<lambda>w. x = y"
abbreviation meqL    :: "\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>" (infixr"\<^bold>=\<^sup>L"52) -- "Leibniz Equality"   
  where "x\<^bold>=\<^sup>Ly \<equiv> \<^bold>\<forall>\<phi>. \<phi>(x)\<^bold>\<rightarrow>\<phi>(y)"
abbreviation mbox   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_"[52]53)
  where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. \<phi>(v)"
abbreviation mdia   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_"[52]53)
  where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. \<phi>(v)"

text {* Finally, a formula is valid if and only if it is satisfied in all worlds. *}

abbreviation valid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"

section {* Axiomatizations of Further Systems *}

text {* Different modal logics can be axiomatized through adding a choice of the following definitions
as axioms: *}
(*
using the \emph{Sahlqvist correspondence}.
The best known logics \emph{K4, K5, KB, K45, KB5, D, D4, D5, D45, ...} are obtained through
the addition of combinations of the following axioms:  *}
*)

abbreviation M 
  where "M \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
abbreviation B 
  where "B \<equiv> \<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>"
abbreviation D 
  where "D \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>"
abbreviation IV 
  where "IV \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>"
abbreviation V 
  where "V \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>"

text {* Because the embedding is of a semantic nature, it is more efficient to instead make use of 
the well-known \emph{Sahlqvist correspondence}, which links these axioms to constraints on a
model's accessibility relation: axioms $M, B, D, IV, V$ impose reflexivity, symmetry, seriality,
transitivity and euclideanness respectively. *}

abbreviation reflexive 
  where "reflexive \<equiv> (\<forall>x. x r x)"
abbreviation symmetric 
  where "symmetric \<equiv> (\<forall>x y. x r y \<longrightarrow> y r x)"
abbreviation serial :: "bool"
  where "serial \<equiv> (\<forall>x. \<exists>y. x r y)"
abbreviation transitive :: "bool"
  where "transitive \<equiv> (\<forall>x y z. ((x r y) \<and> (y r z) \<longrightarrow> (x r z)))"
abbreviation euclidean :: "bool"
  where "euclidean \<equiv> (\<forall>x y z. ((x r y) \<and> (x r z) \<longrightarrow> (y r z)))"

text {* Using these definitions, we can derive axioms for the most common modal logics. Thereby we 
are free to use either the semantic constraints or the related Sahlqvist axioms. Here we provide 
both versions. We recommend to use the semantic constraints. *}

abbreviation D_sem :: bool 
 where "D_sem  \<equiv> serial"
abbreviation D_ax :: bool 
 where "D_ax  \<equiv> \<lfloor>D\<rfloor>"
abbreviation B_sem :: bool 
 where "B_sem  \<equiv> symmetric"
abbreviation B_ax :: bool 
 where "B_ax  \<equiv> \<lfloor>B\<rfloor>"
abbreviation T_sem :: bool
 where "T_sem  \<equiv> reflexive"
abbreviation T_ax :: bool
 where "T_ax  \<equiv> \<lfloor>M\<rfloor>"
abbreviation S4_sem :: bool
 where "S4_sem  \<equiv> reflexive \<and> transitive"
abbreviation S4_ax :: bool
 where "S4_ax  \<equiv>  \<lfloor>M\<rfloor> \<and> \<lfloor>IV\<rfloor> "
abbreviation S5_sem :: bool 
 where "S5_sem  \<equiv> reflexive \<and> euclidean"
abbreviation S5_ax :: bool
 where "S5_ax  \<equiv>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor> "


end
