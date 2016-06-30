theory spatial
imports Main
begin
typedecl n (*Names*)
typedecl P (*Process*)
consts \<^bold>0 :: P


datatype
  'a Procs = Null                             (".0" 115)
           | Plus    "('a Procs) + ('a Procs)"    (infixl ".+" 85)

consts 
      (*     | Out     "'a 'a ('a procs)"         ("_<_>._" [120, 0, 110] 110)
           | In      "'a 'a ('a procs)"         ("_[_]._" [120, 0, 110] 110)
           | Res     "'a ('a procs)"            (".#_ _"  [180, 101] 100)
           | Plus    "('a procs) ('a procs)"    (infixl ".+" 85)
           | Par     "('a procs) ('a procs)"    (infixl ".|" 90)
           | Mt      "'a 'a ('a procs)"         (".[_.=_]_" [100, 100, 96] 95)
           | Mmt     "'a 'a ('a procs)"         (".[_.~=_]_" [100, 100, 96] 95)
           | Repl    "('a procs)"               (".!_" [100] 100)

*)
(*
datatype Processes = \<^bold>0
inductive_set Proc :: "Processes list set" where
  null: \<^bold>0
  input: 
*)
end