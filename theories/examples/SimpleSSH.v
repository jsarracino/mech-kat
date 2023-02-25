Require Import MechKat.NetKAT.

(* three fields: type, switch, and port *)
Inductive fields := | typ | switch | port.
(* 6 vals: port 1/2, switch A/B, SSH, or wildcard (anything) *)
Inductive vals := 
  | one | two 
  | A | B
  | ssh
  | any.

(* if a packet is at A with port two, it should go to B on port one 
   TODO: it still needs:
    packet is at B with port one, should go to A with port two   OR
    packet is at A with port one,    OR 
    packet is at B with port two


*)
Definition topo : kat fields vals := 
  k_and 
    (k_test (t_and (t_check switch A) (t_check port two)))
    (k_and (k_put switch B) (k_put port one)).
