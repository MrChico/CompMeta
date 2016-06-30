theory spatial
imports Main
begin

datatype P = Null | input n n P | lift n P | drop n | par P P  
  and n = quote P

end