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

Theorem contrapositive : forall (P Q: Prop),
  (P -> Q) <-> (~Q -> ~P).
Proof.
intros. unfold iff. apply conj.
- intros. intro. apply H0. apply H. apply H1.
- intros. apply not_not_P. intro. apply H in H1. contradiction.
Qed.

Theorem not_or : forall (P Q: Prop),
  ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
intros. unfold iff. apply conj.
- intros. apply conj. 
  + intro. apply H. left. apply H0.
  + intro. apply H. right. apply H0.
- intros. destruct H as [nP nQ].
  intro. destruct H as [P_|Q_]. contradiction. contradiction.
Qed.

Theorem not_and : forall (P Q: Prop),
  ~(P /\ Q) <-> ~P \/ ~Q.
Proof.
intros. unfold iff. apply conj.
- intros. apply not_not_P. intro. apply not_or in H0. destruct H0 as [P_ Q_].
  apply H. apply not_not_P with (P:=P) in P_. apply not_not_P with (P:=Q) in Q_.
  apply conj. apply P_. apply Q_.
- intros. intro. destruct H0 as [Pt Qt]. destruct H as [Pf|Qf]. contradiction. contradiction.
Qed. 

Theorem iff_iff_compat_l : forall A B C : Prop,
(B <-> C) -> ((A <-> B) <-> (A <-> C)).
Proof.
intros. apply iff_to_and. apply conj.
- intros. apply iff_trans with (B:=B). apply H0. apply H.
- intros. apply iff_trans with (B:=C). apply H0. apply iff_sym. apply H.
Qed.

Theorem iff_iff_compat_r : forall A B C : Prop,
(B <-> C) -> ((B <-> A) <-> (C <-> A)).
Proof.
intros. apply iff_to_and. apply conj.
- intros. apply iff_trans with (B:=B). apply iff_sym. apply H. apply H0.
- intros. apply iff_trans with (B:=C). apply H. apply H0.
Qed.

Theorem and_to_imply : forall A B C : Prop,
  ((A /\ B) -> C) <-> (A -> B -> C).
Proof.
intros. unfold iff. apply conj.
- intros. apply H. apply conj. apply H0. apply H1.
- intros. apply H. apply H0. apply H0.
Qed.