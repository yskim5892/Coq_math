Require Import Relation.
Require Import Ordering.

(* operations *)

Theorem n_plus_identity : forall (n : nat),
  n + 0 = n.
Proof.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed. 

Theorem n_plus_one : forall (n : nat),
  n + 1 = S n.
Proof.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Theorem n_plus_n_Sm : forall (n m : nat),
  n + S m = S (n + m).
Proof.
intros.
induction n. 
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem n_plus_comm : forall (n m : nat),
  n + m = m + n.
Proof.
intros.
induction n.
  - intros. rewrite n_plus_identity. reflexivity.
  - simpl. rewrite IHn. rewrite n_plus_n_Sm. reflexivity.
Qed.

Theorem n_plus_assoc : forall (n m k : nat),
  n + (m + k) = (n + m) + k.
Proof.
intros.
induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem n_plus_cancel : forall (n m k: nat),
  n + k = m + k <-> n = m.
Proof.
intros. unfold iff. apply conj.
- induction k.
  + rewrite n_plus_identity. rewrite n_plus_identity. intros. apply H.
  + intros. rewrite n_plus_n_Sm in H. rewrite n_plus_n_Sm in H. 
    inversion H. apply IHk. apply H1.
- intros. rewrite H. reflexivity.
Qed.

Theorem n_mul_identity : forall n : nat,
  n * 1 = n.
Proof.
induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem n_mul_zero : forall n : nat,
  n * 0 = 0.
Proof.
induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem n_mul_right : forall (n m : nat),
  n * S m = n * m + n.
Proof.
intros.
induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite n_plus_n_Sm. rewrite n_plus_assoc. reflexivity.
Qed.

Theorem n_mul_comm : forall (n m : nat),
  n * m = m * n.
Proof.
intros.
induction n.
  - rewrite n_mul_zero. reflexivity.
  - simpl. rewrite IHn. rewrite n_mul_right. rewrite n_plus_comm. reflexivity.
Qed.

Theorem n_distributive : forall (n m k : nat),
  n * (m + k) = n * m + n * k.
Proof.
intros.
induction n.
  - reflexivity.
  - simpl. 
assert (H : (k + n * (m + k)) = n * m + (k + n * k)).
rewrite IHn. rewrite n_plus_assoc. rewrite n_plus_comm with (n:=k). rewrite n_plus_assoc. reflexivity.
rewrite <- n_plus_assoc. rewrite H. rewrite n_plus_assoc. reflexivity.
Qed.

Theorem n_right_distributive : forall (n m k : nat),
  (n + m) * k = n * k + m * k.
Proof.
intros. rewrite n_mul_comm. rewrite n_mul_comm with (n:=n). rewrite n_mul_comm with (n:=m).
apply n_distributive.
Qed.

Theorem n_mul_assoc : forall (n m k : nat),
  n * (m * k) = (n * m) * k.
Proof.
intros.
induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite n_mul_comm with (n:=m+n*m). rewrite n_distributive. rewrite n_mul_comm.
assert (H : (n*m*k = k*(n*m))).
rewrite n_mul_comm with (m:=n*m). reflexivity.
rewrite H. reflexivity.
Qed.

(* inequalities *)

Definition n_le : Relation nat nat :=
fun p => match p with
  | (n, m) => n <= m
end.

Definition n_lt : Relation nat nat :=
fun p => match p with
  | (n, m) => n < m
end.

Definition n_ge : Relation nat nat :=
fun p => match p with
  | (n, m) => m <= n
end.

Definition n_gt : Relation nat nat :=
fun p => match p with
  | (n, m) => m < n
end.

Theorem n_le_0_n : forall (n : nat),
  0 <= n.
Proof.
induction n.
- apply le_n.
- apply le_S. apply IHn.
Qed.

Theorem n_le_reflexive : forall (n : nat),
  n <= n.
Proof.
intros. apply le_n.
Qed.

Theorem n_le_n_S_m : forall (n m : nat),
  n <= S m <-> n <= m \/ n = S m.
Proof.
unfold iff. intros. apply conj.
- intros. inversion H. 
  + apply or_intror. reflexivity.
  + apply or_introl. apply H1.
- intros. inversion H. 
  + apply le_S. apply H0.
  + rewrite H0. apply le_n.
Qed.

Theorem n_le_transitive : forall (n m k : nat),
  n <= m /\ m <= k -> n <= k.
Proof.
intros. induction k.
- inversion H. inversion H1. rewrite H2 in H0. 
  inversion H0. apply le_n.
- inversion H. apply n_le_n_S_m in H1. inversion H1.
  + apply le_S. apply IHk. apply conj. apply H0. apply H2.
  + rewrite H2 in H0. apply H0.
Qed.

Theorem n_le_Sn_n_false : forall (n : nat),
  not (S n <= n).
Proof.
induction n.
- intros H. inversion H.
- intros H. inversion H.
  + apply IHn. rewrite H1. apply le_n.
  + apply IHn. apply n_le_transitive with (m:= S (S n)).
    apply conj. apply le_S. apply le_n. apply H1.
Qed.

Theorem n_le_Sn_Sm : forall (n m : nat),
  S n <= S m <-> n <= m.
Proof.
unfold iff. intros. apply conj.
- intros. inversion H.
  + apply le_n.
  + apply n_le_transitive with (m:=S n)(k := m).
    apply conj. apply le_S. apply le_n.
    apply H1.
- intros. induction m.
  + inversion H. apply le_n.
  + inversion H. 
    * apply le_n.
    * apply IHm in H1. apply n_le_transitive with (m:=S m).
      apply conj. apply H1. apply le_S. apply le_n.
Qed.

Theorem n_le_antisymmetric : forall (n m : nat),
  n <= m /\ m <= n <-> n = m.
Proof.
unfold iff. intros. apply conj.
- intros. apply proj1 in H as H1. apply proj2 in H as H2.
  inversion H1.
  + reflexivity.
  + assert (contra : S m0 <= m0).
    rewrite <- H3 in H2. apply n_le_transitive with (m:=n).
    apply conj. apply H2. apply H0.
    apply n_le_Sn_n_false in contra. inversion contra.
- intros. apply conj.
  + rewrite H. apply le_n.
  + rewrite H. apply le_n.
Qed.

Theorem n_le_total_ordering : forall (n m : nat),
  n <= m \/ m <= n.
Proof.
intros. induction m.
- right. apply n_le_0_n.
- destruct IHm.
  + left. apply le_S. apply H.
  + inversion H.
    * left. apply le_S. apply le_n.
    * right. apply n_le_Sn_Sm. apply H0.
Qed.

Theorem n_le_total_partial_ordering : total_partial_ordering n_le.
Proof.
unfold total_partial_ordering. apply conj.
- unfold partial_ordering. apply conj.
  + unfold reflexive. apply n_le_reflexive.
  + apply conj.
    * unfold antisymmetric. apply n_le_antisymmetric.
    * unfold transitive. apply n_le_transitive.
- apply n_le_total_ordering.
Qed.

Theorem n_lt_is_strict_n_le : n_lt = partial_to_strict n_le.
Proof.
apply Relation_eq. intros. unfold iff. apply conj.
- intros. unfold partial_to_strict. apply conj.
  + apply n_le_Sn_Sm. apply n_le_transitive with (m:=b). apply conj.
    apply H. apply le_S. apply le_n.
  + intros contra. rewrite contra in H. apply n_le_Sn_n_false in H.
    contradiction.
- intros. unfold partial_to_strict in H. destruct H as [le_a_b neq].
  inversion le_a_b.
  + contradiction.
  + apply n_le_Sn_Sm. apply H.
Qed.

Theorem n_le_is_partial_n_lt : n_le = strict_to_partial n_lt.
Proof.
rewrite n_lt_is_strict_n_le. apply eq_sym. 
apply partial_to_strict_to_partial_identity.
apply n_le_total_partial_ordering.
Qed.

Theorem n_lt_total_strict_ordering : total_strict_ordering n_lt.
Proof.
rewrite n_lt_is_strict_n_le.
apply partial_to_strict_preserves_totality.
apply n_le_total_partial_ordering.
Qed.

Theorem n_le_plus : forall (n m k : nat),
  n <= m <-> n + k <= m + k.
Proof.
unfold iff. intros. apply conj.
- intros. induction k.
  + rewrite n_plus_identity. rewrite n_plus_identity. apply H.
  + rewrite n_plus_n_Sm. rewrite n_plus_n_Sm.
    apply n_le_Sn_Sm. apply IHk.
- intros. induction k.
  + rewrite n_plus_identity in H. rewrite n_plus_identity in H. apply H.
  + rewrite n_plus_n_Sm in H. rewrite n_plus_n_Sm in H.
    apply -> n_le_Sn_Sm in H. apply IHk. apply H.
Qed.

Theorem n_le_mul : forall (n m k : nat),
  n <= m -> n * k <= m * k.
Proof.
intros. induction k.
- rewrite n_mul_zero. rewrite n_mul_zero. apply le_n.
- rewrite n_mul_comm. rewrite n_mul_comm with (n:=m).
  simpl. rewrite n_mul_comm. rewrite n_mul_comm with (m:=m).
  apply n_le_transitive with (m:=n+m*k). apply conj.
  + rewrite n_plus_comm. rewrite n_plus_comm with (n:=n).
    apply n_le_plus. apply IHk.
  + apply n_le_plus. apply H.
Qed. 

Theorem n_le_sum : forall (n m k l : nat),
  n <= m /\ k <= l -> n + k <= m + l.
Proof.
intros. destruct H as [nm kl].
apply n_le_transitive with (m:=m+k). split.
- apply n_le_plus. apply nm.
- rewrite n_plus_comm. rewrite n_plus_comm with (n:=m).
  apply n_le_plus. apply kl.
Qed.

Theorem n_lt_plus : forall (n m k : nat),
  n < m <-> n + k < m + k.
Proof.
intros. unfold lt.
rewrite n_plus_comm. rewrite <- n_plus_n_Sm. rewrite n_plus_comm.
apply n_le_plus.
Qed.

Theorem n_lt_mul : forall (n m k : nat),
  n < m /\ 0 < k -> n * k < m * k.
Proof.
intros. unfold lt. destruct H as [nm kpos]. apply n_le_mul with (k:=k) in nm.
simpl in nm. rewrite n_plus_comm in nm. apply n_le_transitive with (m:=n*k+k). apply conj.
- rewrite <- n_plus_one. rewrite n_plus_comm. rewrite n_plus_comm with (m:=k).
  apply n_le_plus. apply kpos.
- apply nm.
Qed.

Theorem n_le_lt_sum : forall (n m k l : nat),
  n < m /\ k <= l -> n + k < m + l.
Proof.
intros. destruct H as [nm kl].
unfold lt. rewrite n_plus_comm. rewrite <- n_plus_n_Sm. rewrite n_plus_comm.
apply n_le_sum. apply conj. apply nm. apply kl.
Qed.

Theorem n_lt_sum : forall (n m k l : nat),
  n < m /\ k < l -> n + k < m + l.
Proof.
intros. unfold lt. rewrite <- n_plus_n_Sm. apply n_le_lt_sum in H.
unfold lt in H. apply le_S in H. apply n_le_Sn_Sm. apply H.
Qed.

Theorem n_lt_lemma1 : forall (n m k l : nat),
  n < m /\ k < l -> n * l + m * k < n * k + m * l.
Proof.
intros. induction l.
- apply proj2 in H. inversion H.
- rewrite <- n_plus_one. rewrite n_distributive. rewrite n_distributive.
  rewrite n_mul_identity. rewrite n_mul_identity.
  destruct H as [nm kSl]. inversion kSl.
  + rewrite n_plus_comm with (m:=m). rewrite n_plus_assoc. apply n_lt_plus.
    rewrite n_plus_comm. rewrite n_plus_comm with (m:=m). apply n_lt_plus.
    apply nm.
  + rewrite <- n_plus_assoc. rewrite n_plus_comm with (n:=n).
    rewrite n_plus_assoc. rewrite n_plus_assoc.
    apply n_lt_sum. apply conj. apply IHl. 
    apply conj. apply nm. apply H0. apply nm.
Qed.