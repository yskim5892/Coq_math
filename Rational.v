Require Import Logic_utils.
Require Import Relation.
Require Import Ordering.
Require Import NatProps.
Require Import Integer.

Inductive ZxZ : Type :=
  | q (a b : Z).

Definition Q (r : ZxZ) : Prop :=
match r with
| q a b => z_0 <z b
end.

Axiom q_eq : forall (a b c d : Z),
  b <> z_0 /\ d <> z_0 /\ z_mul a d = z_mul b c <-> q a b = q c d.

Definition q_plus (r s : ZxZ) : ZxZ :=
match r with
| q a b => match s with
  | q c d => q ((a *z d) +z (b *z c)) (b *z d)
  end
end.

Definition q_neg (r : ZxZ) : ZxZ :=
match r with
| q a b => q (-z a) b
end.

Definition q_minus (r s : ZxZ) : ZxZ :=
  q_plus r (q_neg s).

Definition q_mul (r s : ZxZ) : ZxZ :=
match r with 
| q a b => match s with
  | q c d => q (a *z c) (b *z d)
  end
end.

Definition q_inv (r : ZxZ) : ZxZ :=
match r with
| q a b => q b a
end.

Definition q_div (r : ZxZ)(s : ZxZ) : ZxZ :=
  q_mul r (q_inv s).

Definition q_0 := q z_0 z_1.
Definition q_1 := q z_1 z_1.
Notation "r +q s" := (q_plus r s) (at level 50, left associativity).
Notation "r -q s" := (q_minus r s) (at level 50, left associativity).
Notation "r *q s" := (q_mul r s) (at level 40, left associativity).
Notation "r /q s" := (q_div r s) (at level 40, left associativity).
Notation "-q r" := (q_neg r) (at level 35, right associativity).
Notation "r ^-1q" := (q_inv r) (at level 35, right associativity).

Theorem q_nonzero : forall (r : ZxZ),
  Q r /\ r <> q_0 ->  match r with
    | q a b => a <> z_0 /\ z_0 <z b
end.
Proof.
intros. destruct r. unfold Q in H. apply conj. destruct H as [Qr neqr0].
intros aeq0. apply neqr0. rewrite aeq0. apply q_eq. apply conj. 
- intro. rewrite H in Qr. simpl in Qr. inversion Qr.
- apply conj. discriminate. rewrite z_mul_zero. rewrite z_mul_comm. rewrite z_mul_zero. reflexivity.
- apply H.
Qed.

Theorem q_reduction : forall (a b c : Z),
  b <> z_0 /\ c <> z_0 -> q a b = q (z_mul a c)(z_mul b c).
Proof.
intros. apply q_eq. apply conj. apply H.
apply conj. apply z_mul_a_b_nonzero. apply H.
rewrite z_mul_comm. rewrite z_mul_comm with (a:=a).
rewrite z_mul_assoc. reflexivity.
Qed.

Theorem q_closed_under_plus : forall (r s : ZxZ),
  Q r /\ Q s -> Q (r +q s).
Proof.
destruct r, s. unfold q_plus. unfold Q. intro.
apply z_lt_mul in H. rewrite z_mul_comm in H. rewrite z_mul_zero in H. apply H.
Qed. 

Theorem q_closed_under_mul : forall (r s : ZxZ),
  Q r /\ Q s -> Q (r *q s).
Proof.
destruct r, s. unfold q_mul. unfold Q. intro.
apply z_lt_mul in H. rewrite z_mul_comm in H. rewrite z_mul_zero in H. apply H.
Qed.

Theorem q_closed_under_neg : forall (r : ZxZ),
  Q r -> Q (-q r).
Proof.
destruct r. unfold q_neg. unfold Q. intro. apply H.
Qed.

Theorem q_closed_under_inv : forall (r : ZxZ),
  Q r /\ r <> q_0 -> Q (r ^-1q).
Proof.
destruct r. intro. apply q_nonzero in H. 
pose (H0 := z_lt_total_strict_ordering). destruct H0 as [strict total].
destruct (total z_0 a) as [a_pos | a_neg].
- unfold q_inv. unfold Q. apply a_pos.
- destruct a_neg as [a_neg | a0]. 
  + unfold q_inv. rewrite q_reduction with (c:=-z z_1). 
    rewrite z_mul_neg. rewrite z_mul_neg. rewrite z_mul_identity. rewrite z_mul_identity.
    unfold Q. apply z_lt_neg in a_neg. apply a_neg. apply conj. apply H. intro. discriminate.
  + apply eq_sym in a0. apply H in a0. contradiction.
Qed.

Theorem q_eq_neg : forall (r s : ZxZ),
  -qr = -qs -> r = s.
Proof.
destruct r, s. simpl.
intros. apply q_eq in H. apply q_eq. apply conj. apply H. apply conj. apply H.
apply proj2 in H. apply proj2 in H. rewrite z_mul_neg in H. rewrite z_mul_comm in H.
rewrite z_mul_neg in H. apply z_eq_neg in H. rewrite z_mul_comm in H. apply H.
Qed.

Theorem q_eq_inv : forall (r s : ZxZ),
  Q r /\ Q s /\ r ^-1q = s ^-1q -> r = s.
Proof.
destruct r, s. unfold Q.
intro. apply q_eq. apply conj. apply z_pos_nonzero. apply H. apply conj. apply z_pos_nonzero. apply H.
apply proj2 in H. apply proj2 in H. apply q_eq in H. apply eq_sym. apply H.
Qed.

Theorem q_plus_identity : forall (r : ZxZ),
   r +q q_0 = r.
Proof.
intros. destruct r. simpl.
rewrite z_mul_zero. rewrite z_mul_identity.
rewrite z_plus_identity. rewrite z_mul_identity. reflexivity.
Qed.

Theorem q_plus_inverse : forall (r : ZxZ),
  Q r -> r +q -qr = q_0.
Proof.
intros. destruct r. simpl. apply q_eq. unfold Q in H.
apply conj.
- apply z_mul_a_b_nonzero. apply conj. apply z_pos_nonzero. apply H. apply z_pos_nonzero. apply H.
- apply conj. intro. discriminate. 
  rewrite z_mul_zero. rewrite z_mul_neg. rewrite z_mul_comm with (a:=a).
  rewrite z_plus_inverse. reflexivity.
Qed.

Theorem q_plus_comm : forall (r s : ZxZ),
  r +q s = s +q r.
Proof.
intros. destruct r, s. simpl.
rewrite z_mul_comm. rewrite z_mul_comm with (a:=b). rewrite z_mul_comm with (a:=b).
rewrite z_plus_comm. reflexivity.
Qed.

Theorem q_plus_assoc : forall (r s t : ZxZ),
  (r +q s) +q t = r +q (s +q t).
Proof.
intros. destruct r, s, t. simpl.
rewrite z_distributive with (a:=b). rewrite z_mul_comm. rewrite z_distributive with (a:=b1). rewrite z_plus_assoc.
rewrite z_mul_comm with (a:=b1). rewrite z_mul_assoc with (a:=a).
rewrite z_mul_comm with (a:=b1). rewrite z_mul_assoc with (a:=b).
rewrite z_mul_comm with (a:=b). rewrite z_mul_assoc with (a:=b).
rewrite z_mul_assoc with (a:=b). reflexivity.
Qed.

Theorem q_plus_cancel : forall (r s t : ZxZ),
  r +q t = s +q t -> r = s.
Proof.
intros. destruct r, s, t. simpl in H. apply q_eq in H. destruct H as [nonzero H].
apply <- z_mul_a_b_nonzero in nonzero. destruct nonzero as [bn0 b1n0]. destruct H as [nonzero H].
apply <- z_mul_a_b_nonzero in nonzero. destruct nonzero as [b0n0].
apply q_eq. apply conj. apply bn0. apply conj. apply b0n0.
rewrite z_mul_assoc in H. rewrite <- z_mul_assoc with (a:=b) in H. rewrite z_mul_comm with (a:=b1) in H.
rewrite z_mul_assoc in H. 
assert ((a *z b1 +z b *z a1) *z b0 = b *z (a0 *z b1 +z b0 *z a1)).
{ apply z_mul_cancel with (c:=b1). apply conj. apply H. apply b1n0. }
rewrite z_mul_comm in H1. rewrite z_distributive in H1. rewrite z_distributive in H1.
rewrite z_mul_assoc with (c:=a1) in H1. rewrite z_mul_assoc with (c:=a1) in H1.
rewrite z_mul_comm with (b:=b) in H1. apply z_plus_cancel in H1.
rewrite z_mul_assoc in H1. rewrite z_mul_assoc in H1.
apply z_mul_cancel with (c:=b1). apply conj.
rewrite z_mul_comm with (a:=a). apply H1. apply b1n0.
Qed. 

Theorem q_mul_identity : forall (r : ZxZ),
  r *q q_1 = r.
Proof.
intros. destruct r. simpl.
rewrite z_mul_identity. rewrite z_mul_identity.
reflexivity.
Qed.

Theorem q_mul_inverse : forall (r : ZxZ),
  Q r /\ r <> q_0 -> r *q r ^-1q = q_1.
Proof.
intros. destruct r. simpl. apply q_nonzero in H. apply q_eq. apply conj.
apply z_mul_a_b_nonzero. apply conj. apply z_pos_nonzero. apply H. apply H.
apply conj. discriminate. rewrite z_mul_identity. rewrite z_mul_identity. apply z_mul_comm.
Qed.

Theorem q_mul_zero : forall (r : ZxZ),
  Q r -> r *q q_0 = q_0.
Proof.
intros. destruct r. simpl. unfold Q in H.
rewrite z_mul_zero. rewrite z_mul_identity. apply q_eq.
apply conj. apply z_pos_nonzero. apply H. apply conj. intro. discriminate.
rewrite z_mul_zero. rewrite z_mul_comm. rewrite z_mul_zero. reflexivity.
Qed.

Theorem q_mul_neg : forall (r s : ZxZ),
  Q r /\ Q s -> r *q (-qs) = -q(r *q s).
Proof.
destruct r, s. unfold Q. intros. apply q_eq.
assert (b *z b0 <> z_0).
{ apply z_mul_a_b_nonzero. apply conj. apply z_pos_nonzero. apply H. apply z_pos_nonzero. apply H. }
apply conj. apply H0. apply conj. apply H0.
rewrite z_mul_comm. rewrite z_mul_neg. rewrite z_mul_neg. reflexivity.
Qed.

Theorem q_mul_comm : forall (r s : ZxZ),
  r *q s = s *q r.
Proof.
intros. destruct r, s. simpl.
rewrite z_mul_comm. rewrite z_mul_comm with (a:=b). reflexivity.
Qed.

Theorem q_distributive : forall (r s t : ZxZ),
  Q r /\ Q s /\ Q t -> r *q (s +q t) = (r *q s) +q (r *q t).
Proof.
intros. destruct r, s, t. simpl. unfold Q in H.

rewrite z_mul_assoc with (a:=z_mul a a0). rewrite z_mul_comm with (a:=z_mul a a0).
rewrite <- z_mul_assoc with (b:=z_mul a a0). 
rewrite <- z_mul_assoc with (c:=z_mul a a1).
rewrite <- z_distributive.
rewrite <- z_mul_assoc with (c:=z_mul b b1).
rewrite z_mul_comm with (b:=a*za0*zb1+zb0*z(a*za1)). rewrite z_mul_comm with (b:=b0*z(b*zb1)).
rewrite <- q_reduction.

rewrite <- z_mul_assoc. rewrite z_mul_assoc with (a:=b0). rewrite z_mul_comm with (a:=b0)(b:=a).
rewrite <- z_mul_assoc with (c:=a1).
rewrite <- z_distributive.
rewrite z_mul_comm with (b:=z_mul b0 b1).
rewrite z_mul_comm with (a:=b).
rewrite z_mul_assoc with (a:=b0).
reflexivity.

apply conj. apply z_mul_a_b_nonzero. apply conj. apply z_pos_nonzero. apply H.
apply z_mul_a_b_nonzero. apply conj. apply z_pos_nonzero. apply H. apply z_pos_nonzero. apply H. apply z_pos_nonzero. apply H.
Qed.

Theorem q_mul_assoc : forall (r s t : ZxZ),
  Q r /\ Q s /\ Q t -> r *q (s *q t) = (r *q s) *q t.
Proof.
destruct r, s, t. unfold Q. intros. apply q_eq.
assert (b <> z_0 /\ b0 <> z_0 /\ b1 <> z_0).
{ apply conj. apply z_pos_nonzero. apply H. apply conj. apply z_pos_nonzero. apply H. apply z_pos_nonzero. apply H. }

apply conj. apply z_mul_a_b_nonzero. apply conj. apply H0. apply z_mul_a_b_nonzero. apply H0.
apply conj. apply z_mul_a_b_nonzero. apply conj. apply z_mul_a_b_nonzero. apply conj. apply H0. apply H0. apply H0.
rewrite z_mul_comm. rewrite z_mul_assoc with (c:=b1). rewrite z_mul_assoc with (c:=a1). reflexivity.
Qed.