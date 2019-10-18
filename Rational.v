Require Import NatProps.
Require Import Integer.

Inductive Q : Type :=
  | q (a b : Z).

Axiom q_eq : forall (a b c d : Z),
  z_mul a d = z_mul b c -> q a b = q c d.

Definition q_plus (r : Q)(s : Q) : Q :=
match r with
| q a b => match s with
  | q c d => q (z_plus (z_mul a d) (z_mul b c)) (z_mul b d)
  end
end.

Definition q_neg (r : Q) : Q :=
match r with
| q a b => q (z_neg a) b
end.

Definition q_mul (r : Q)(s : Q) : Q :=
match r with 
| q a b => match s with
  | q c d => q (z_mul a c) (z_mul b d)
  end
end.

Definition z2q (a : Z) : Q := q a z_1.

Definition q_0 := q z_0 z_1.
Definition q_1 := q z_1 z_1.

Theorem q_plus_identity : forall (r : Q),
  q_plus r q_0 = r.
Proof.
intros. destruct r. simpl.
rewrite z_mul_zero. rewrite z_mul_identity.
rewrite z_plus_identity. rewrite z_mul_identity. reflexivity.
Qed.

Theorem q_plus_comm : forall (r s : Q),
  q_plus r s = q_plus s r.
Proof.
intros. destruct r, s. simpl.
rewrite z_mul_comm. rewrite z_mul_comm with (a:=b). rewrite z_mul_comm with (a:=b).
rewrite z_plus_comm. reflexivity.
Qed.

Theorem q_plus_assoc : forall (r s t : Q),
  q_plus (q_plus r s) t = q_plus r (q_plus s t).
Proof.
intros. destruct r, s, t. simpl.
assert (H : forall (c d c0 d0 c1 d1 : Z),
z_plus (z_mul(z_plus(z_mul c d0) (z_mul d c0)) d1) (z_mul (z_mul d d0) c1) =
z_plus (z_mul c (z_mul d0 d1)) (z_mul d (z_plus (z_mul c0 d1) (z_mul d0 c1)))).

intros.
rewrite z_distributive with (a:=d). rewrite z_mul_comm. rewrite z_distributive with (a:=d1).
rewrite z_plus_assoc.
rewrite z_mul_comm with (a:=d1). rewrite z_mul_assoc with (a:=c).
rewrite z_mul_comm with (a:=d1). rewrite z_mul_assoc with (a:=d).
rewrite z_mul_comm with (a:=d). rewrite z_mul_assoc with (a:=d).
reflexivity.

rewrite H.
rewrite z_mul_assoc with (a:=b). reflexivity.
Qed.

Theorem q_mul_identity : forall (r : Q),
  q_mul r q_1 = r.
Proof.
intros. destruct r. simpl.
rewrite z_mul_identity. rewrite z_mul_identity.
reflexivity.
Qed.

Theorem q_mul_zero : forall (r : Q),
  q_mul r q_0 = q_0.
Proof.
intros. destruct r. simpl.
rewrite z_mul_zero. rewrite z_mul_identity.
apply q_eq.
rewrite z_mul_zero. rewrite z_mul_identity. reflexivity.
Qed.

Theorem q_mul_comm : forall (r s : Q),
  q_mul r s = q_mul s r.
Proof.
intros. destruct r, s. simpl.
rewrite z_mul_comm. rewrite z_mul_comm with (a:=b). reflexivity.
Qed.

Theorem q_reduction : forall (a b c : Z),
  q a b = q (z_mul c a)(z_mul c b).
Proof.
intros. apply q_eq. rewrite z_mul_comm. rewrite z_mul_comm with (a:=c).
rewrite z_mul_assoc. reflexivity.
Qed.

Theorem q_distributive : forall (r s t : Q),
  q_mul r (q_plus s t) = q_plus (q_mul r s) (q_mul r t).
Proof.
intros. destruct r, s, t. simpl.
rewrite z_mul_assoc with (a:=z_mul a a0). rewrite z_mul_comm with (a:=z_mul a a0).
rewrite <- z_mul_assoc with (b:=z_mul a a0). 
rewrite <- z_mul_assoc with (c:=z_mul a a1).
rewrite <- z_distributive.
rewrite <- z_mul_assoc with (c:=z_mul b b1).
rewrite <- q_reduction.

rewrite <- z_mul_assoc. rewrite z_mul_assoc with (a:=b0). rewrite z_mul_comm with (a:=b0)(b:=a).
rewrite <- z_mul_assoc with (c:=a1).
rewrite <- z_distributive.
rewrite z_mul_comm with (b:=z_mul b0 b1).
rewrite z_mul_comm with (a:=b).
rewrite z_mul_assoc with (a:=b0).
reflexivity.
Qed.