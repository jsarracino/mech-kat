
Section NetKAT.
  Variable (Fields: Type).
  Variable (Vals: Type).

  Inductive test := 
  | t_unit | t_fail (* 1 and 0 *)
  | t_check : Fields -> Vals -> test (* f = v *)
  | t_or : test -> test -> test (* l + r *)
  | t_and : test -> test -> test (* l . r *)
  | t_neg : test -> test. (* ! t *)

  Inductive kat := 
  | k_test : test -> kat
  | k_put : Fields -> Vals -> kat (* f <- v *)
  | k_or : kat -> kat -> kat (* l + r *)
  | k_and : kat -> kat -> kat (* l . r *)
  | k_star : kat -> kat  (* x^* *)
  | k_dup : kat.

  (* non-empty lists *)
  Inductive ne_list (V: Type) : Type := 
  | ne_nil : V -> ne_list V (* p :: <> *)
  | ne_cons : V -> ne_list V -> ne_list V. (* p :: h *)

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
  Fixpoint interp_test (t: test) (h: history) := 
    match t with 
    | t_unit => True
    | t_fail => False
    | t_check f v => (* syntax for pkt . f = v *)
      match h with 
      | ne_nil p => 
        p f = v  (* semantics for pkt . f = v when the history is pkt :: <> *)
      | ne_cons p _ => 
        p f = v  (* semantics for pkt . f = v when the history is pkt :: h' *)
      end
    | t_or t_l t_r => 
      interp_test t_l h \/ interp_test t_r h
    | t_and t_l t_r => 
      interp_test t_l h /\ interp_test t_r h
    | t_neg t => 
      ~ interp_test t h
    end.
  

  (* Two tests are equivalent (i.e. KAT equal) if they have identical behavior on histories *)
  Definition equiv_test (l r : test) : Prop := 
    forall h, 
      interp_test l h <-> interp_test r h.

  Lemma ba_seq_idem : 
    forall x, 
      equiv_test (t_and x x) x.
  Proof.
    unfold equiv_test.
    intros.
    split; intros.
    - simpl in H.
      intuition.
    - simpl.
      intuition.
  Qed.

  Require Import Coq.Classes.EquivDec.

  Context `{FEqDec: EquivDec.EqDec Fields eq}.

  Definition pkt_put (p: pkt) f v := fun f' => 
    if f' == f then v else p f'.

  Inductive interp_kat : kat -> history -> history -> Prop := 
  | interp_k_test : 
    forall t h, 
      interp_test t h -> 
      interp_kat (k_test t) h h
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

  Require Import Coq.Logic.FunctionalExtensionality.

  Lemma put_pkt_iota : 
    forall p f,
      pkt_put p f (p f) = p.
  Proof.
    intros.
    extensionality x.
    unfold pkt_put.
    destruct (_ == _) eqn:?.
    - inversion e;
      subst.
      trivial.
    - trivial.
  Qed.

  Lemma check_put : 
    forall f v h,
      interp_test (t_check f v) h -> 
      interp_kat (k_put f v) h h.
  Proof.
    intros.
    simpl in H.
    destruct h;
    subst.
    - assert (p = pkt_put p f (p f)) by now erewrite put_pkt_iota.
      erewrite H at 3.
      econstructor.
    - assert (p = pkt_put p f (p f)) by now erewrite put_pkt_iota.
      erewrite H at 3.
      econstructor.
  Qed.

  Lemma put_inj:
    forall f v pre post post', 
      interp_kat (k_put f v) pre post -> 
      interp_kat (k_put f v) pre post' -> 
      post = post'.
  Proof.
    destruct pre;
    intros;
    inversion H; subst;
    inversion H0; subst;
    trivial.
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
      pose proof (check_put _ _ _ H2).
      assert (post = post0) by (eapply put_inj; eauto).
      subst.
      econstructor.
      trivial.
    - inversion H; subst.
      clear H.
      econstructor.
      split; try econstructor;
      try eapply check_put;
      trivial.
  Qed.
End NetKAT.

Arguments t_unit {_ _}.
Arguments t_fail {_ _}.
Arguments t_check {_ _}.
Arguments t_or {_ _}.
Arguments t_and {_ _}.
Arguments t_neg {_ _}.

Arguments k_test {_ _}.
Arguments k_put {_ _}.
Arguments k_or {_ _}.
Arguments k_and {_ _}.
Arguments k_star {_ _}.
Arguments k_dup {_ _}.