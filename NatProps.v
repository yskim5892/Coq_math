Theorem n_plus_identity : forall (n : nat),
  n + 0 = n.
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

Theorem n_plus_remove : forall (n m k: nat),
  n + m = n + k -> m = k.
Proof.
intros.
induction n.
  - simpl in H. apply H.
  - simpl in H. inversion H. apply IHn. apply H1.
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
