Axiom law_of_excluded_middle : forall (P : Prop), P \/ ~P.

Theorem neq_comm : forall (A: Type)(a b : A), a <> b -> b <> a.
Proof.
intros. unfold not. intros. rewrite H0 in H. apply H. reflexivity.
Qed.

Theorem de_morgan1 : forall (P Q R : Prop),
  (P \/ Q) /\ R -> (P /\ R) \/ (Q /\ R).
Proof.
intros. destruct H. inversion H.
- apply or_introl. apply conj. apply H1. apply H0.
- apply or_intror. apply conj. apply H1. apply H0.
Qed.

Theorem de_morgan2 : forall (P Q R : Prop),
  (P /\ Q) \/ R -> (P \/ R) /\ (Q \/ R).
Proof.
intros. apply conj.
- inversion H.
  + apply proj1 in H0. apply or_introl. apply H0.
  + apply or_intror. apply H0.
- inversion H.
  + apply proj2 in H0. apply or_introl. apply H0.
  + apply or_intror. apply H0.
Qed.

Theorem reduce_or_P_and_notP : forall (P Q : Prop),
  (Q \/ P) /\ ~P -> Q.
Proof.
intros. apply de_morgan1 in H. inversion H.
- apply H0.
- apply proj1 in H0 as H1. apply proj2 in H0 as H2. contradiction.
Qed.

Theorem not_not_P : forall (P :Prop),
  not (not P) <-> P.
Proof.
intros. assert (lem : P \/ ~P).
{ apply law_of_excluded_middle. }
inversion lem.
- unfold iff. apply conj.
  + intros. apply H.
  + intros. intros H1. contradiction.
- unfold iff. apply conj.
  + intros. contradiction.
  + intros. contradiction.
Qed.