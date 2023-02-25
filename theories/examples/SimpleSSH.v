Require Import MechKat.NetKAT.

(* three fields: type, switch, and port *)
Inductive fields := | typ | switch | port.
(* 6 vals: port 1/2, switch A/B, SSH, or wildcard (anything) *)
Inductive vals := 
  | one | two 
  | A | B
  | ssh
  | any.

(* if a packet is at A with port two, it should go to B on port one *)
Definition topo := 
  k_and 
    (k_test (t_and (t_check switch A) (t_check port two)))
    (k_and (k_put switch B) (k_put port one)).
