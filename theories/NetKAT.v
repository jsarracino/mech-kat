

Unset Positivity Checking.

Section NetKAT.
  Variable (Fields: Type).
  Variable (Vals: Type).

  Inductive test := 
  | t_unit | t_fail
  | t_check : Fields -> Vals -> test 
  | t_or : test -> test -> test
  | t_and : test -> test -> test
  | t_neg : test -> test.

  Inductive kat := 
  | k_test : test -> kat
  | k_put : Fields -> Vals -> kat
  | k_or : kat -> kat -> kat
  | k_and : kat -> kat -> kat
  | k_star : kat -> kat 
  | k_dup : kat.

  (* non-empty lists *)
  Inductive ne_list (V: Type) : Type := 
  | ne_nil : V -> ne_list V
  | ne_cons : V -> ne_list V -> ne_list V.

  Arguments ne_nil {_}.
  Arguments ne_cons {_}.

  Fixpoint ne_app {V} (l r: ne_list V) := 
    match l with 
    | ne_nil x => ne_cons x r
    | ne_cons x l => 
      ne_cons x (ne_app l r)
    end.

  (* packets are maps from fields to values *)
  Definition pkt := Fields -> Vals.
  Definition history := ne_list pkt.

  (* An interpretation relates tests/kats with input/output histories.
     Notice that the original paper maps to a powerset; the intuition here is that interp_test t pre post is true for all possible histories post in the powerset of the paper's interp definition.
  *)
  (* #[ bypass_check(positivity=yes) ] *)
  Inductive interp_test : test -> history -> Prop := 
  | interp_tu : forall h, interp_test t_unit h
  | interp_check_nil : 
    forall pkt f v, 
      pkt f = v -> 
      interp_test (t_check f v) (ne_nil pkt)
  | interp_check_cons : 
    forall pkt h f v, 
      pkt f = v -> 
      interp_test (t_check f v) (ne_cons pkt h)
  | interp_t_or : 
    forall t_l t_r h,
      interp_test t_l h \/ interp_test t_r h ->
      interp_test (t_or t_l t_r) h
  | interp_t_and : 
    forall t_l t_r h,
      interp_test t_l h /\ interp_test t_r h -> 
      interp_test (t_and t_l t_r) h
  | interp_neg: forall t h, 
    (~ interp_test t h) -> (* this is the definition that angers the positivity checker, since ~ A unfolds to (A -> False ). *)
    interp_test (t_neg t) h.
  

  (* Two tests are equivalent (i.e. KAT equal) if they have identical behavior on histories *)
  Definition equiv_test l r := 
    forall h, interp_test l h <-> interp_test r h.

  Lemma ba_seq_idem : 
    forall x, 
      equiv_test (t_and x x) x.
  Proof.
    unfold equiv_test.
    intros.
    split; intros.
    - inversion H; subst.
      intuition.
    - econstructor.
      intuition.
  Qed.

  Require Import Coq.Classes.EquivDec.

  Context `{FEqDec: EquivDec.EqDec Fields eq}.

  Definition pkt_put (p: pkt) f v := fun f' => 
    if f' == f then v else p f'.

  Inductive interp_kat : kat -> history -> history -> Prop := 
  | interp_k_test : 
    forall t pre post, 
      interp_test t post -> 
      interp_kat (k_test t) pre post
  | interp_put_nil : 
    forall p f v, 
      interp_kat (k_put f v) (ne_nil p) (ne_nil (pkt_put p f v))
  | interp_put_cons : 
    forall p h f v, 
      interp_kat (k_put f v) (ne_cons p h) (ne_cons (pkt_put p f v) h)
  | interp_k_or : 
    forall k_l k_r pre post,
      interp_kat k_l pre post \/ interp_kat k_r pre post ->
      interp_kat (k_or k_l k_r) pre post
  | interp_k_and : 
    forall k_l k_r pre post post',
      interp_kat k_l pre post /\ interp_kat k_r post post' -> 
      interp_kat (k_and k_l k_r) pre post'
  | interp_star_one : 
    forall k pre post,
      interp_kat k pre post -> 
      interp_kat (k_star k) pre post
  | interp_star_many : 
    forall k pre post post',
      interp_kat k pre post -> 
      interp_kat (k_star k) post post' -> 
      interp_kat (k_star k) pre post'
  | interp_dup_nil : 
    forall p, interp_kat k_dup (ne_nil p) (ne_cons p (ne_nil p))
  | interp_dup_cons : 
    forall p h, interp_kat k_dup (ne_cons p h) (ne_cons p (ne_cons p h)).

  Definition equiv_kat l r :=
    forall pre post, 
      interp_kat l pre post <-> interp_kat r pre post.

  Lemma put_pkt_iota : 
    forall p f v,
      pkt_put p f (p v) = p.
  Admitted.

  Lemma check_put : 
    forall f v h,
      interp_test (t_check f v) h -> 
      interp_kat (k_put f v) h h.
  Proof.
    intros.
    inversion H; subst; clear H.
    - assert (pkt0 = pkt_put pkt0 f (pkt0 f)) by now erewrite put_pkt_iota.
      erewrite H at 3.
      econstructor.
    - assert (pkt0 = pkt_put pkt0 f (pkt0 f)) by now erewrite put_pkt_iota.
      erewrite H at 3.
      econstructor.
  Qed.

  Lemma pa_filter_mod : 
    forall f v,
      equiv_kat 
        (k_and (k_test (t_check f v)) (k_put f v)) 
        (k_test (t_check f v)).
  Proof.
    unfold equiv_kat.
    intros;
    split;
    intros.
    - inversion H; subst;
      clear H.
      destruct H4.
      inversion H; subst.
      clear H.
      inversion H0;
      subst;
      clear H0;
      repeat econstructor;
      unfold pkt_put;
      destruct (_ == _) eqn:?;
      congruence.
    - inversion H; subst.
      clear H.
      econstructor.
      split.
      econstructor.
      eapply H1.
      eapply check_put.
      trivial.
  Qed.
End NetKAT.
