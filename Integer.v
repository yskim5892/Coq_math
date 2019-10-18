Require Import NatProps.
Inductive Z : Type :=
  | z ( n m : nat).

Axiom z_eq : forall (n1 n2 m1 m2 : nat),
n1 + m2 = n2 + m1 -> z n1 n2 = z m1 m2.

Definition z_plus (z1 : Z)(z2 : Z) : Z :=
  match z1 with 
  | z a b => match z2 with
    | z c d => z (a+c) (b+d)
    end
  end.

Definition z_neg (z1 : Z) : Z :=
  match z1 with
  | z a b => z b a
  end.

Definition z_minus (z1 : Z)(z2 : Z) :=
  z_plus z1 (z_neg z2).

Definition z_mul (z1 : Z)(z2 : Z) :=
  match z1 with
  | z a b => match z2 with
    | z c d => z (a*c + b*d) (a*d + b*c)
    end
  end.

Definition z_0 := z 0 0.
Definition z_1 := z 1 0.

Theorem z_plus_identity : forall (a : Z),
  z_plus a z_0 = a.
Proof.
intros. destruct a. simpl. rewrite n_plus_identity. rewrite n_plus_identity with (n:=m). reflexivity.
Qed.

Theorem z_plus_comm : forall (a b : Z),
  z_plus a b = z_plus b a.
Proof.
destruct a, b. simpl. rewrite n_plus_comm. rewrite n_plus_comm with (n:=m0). reflexivity. 
Qed.

Theorem z_plus_assoc : forall (a b c : Z),
  z_plus (z_plus a b) c = z_plus a (z_plus b c).
Proof.
intros. destruct a, b, c. simpl. rewrite n_plus_assoc. rewrite n_plus_assoc with (n:=m). reflexivity.
Qed.

Theorem z_mul_identity : forall (a : Z),
  z_mul a z_1 = a.
Proof.
intros. destruct a. simpl. 
rewrite n_mul_identity. rewrite n_mul_identity with (n:=m).
rewrite n_mul_zero. rewrite n_mul_zero. simpl.
rewrite n_plus_identity. reflexivity.
Qed.

Theorem z_mul_zero : forall (a : Z),
  z_mul a z_0 = z_0.
Proof.
intros. destruct a. simpl. 
rewrite n_mul_zero. rewrite n_mul_zero.
rewrite n_plus_identity. reflexivity.
Qed.

Theorem z_mul_comm : forall (a b : Z),
  z_mul a b = z_mul b a.
Proof.
intros. destruct a, b. simpl.
rewrite n_mul_comm. rewrite n_mul_comm with(n:=m).
rewrite n_mul_comm with (m:=m0). rewrite n_mul_comm with (m:=n0). 
rewrite n_plus_comm with (n:=m0*n). reflexivity.
Qed.

Theorem z_distributive : forall (a b c : Z),
  z_mul a (z_plus b c) = z_plus (z_mul a b) (z_mul a c).
Proof.
intros. destruct a, b, c. simpl.
assert (H: forall (k k0 k1 l l0 l1: nat),
  k * (k0 + k1) + l * (l0 + l1) = k * k0 + l * l0 + (k * k1 + l * l1)).
intros.
rewrite n_distributive with (n:=k). rewrite n_distributive with (n:=l).
rewrite n_plus_assoc. rewrite <- n_plus_assoc with (k:=l*l0). rewrite n_plus_comm with (n:=k*k1).
rewrite n_plus_assoc. rewrite <- n_plus_assoc with (k:=l*l1). reflexivity.

rewrite H. rewrite H with (k:=n)(l:=m). reflexivity.
Qed.

Theorem z_mul_assoc : forall (a b c : Z),
  z_mul a (z_mul b c) = z_mul(z_mul a b) c.
Proof.
intros. destruct a, b, c. simpl.
assert (H : forall (k k0 k1 l l0 l1: nat), 
  k * (k0 * k1 + l0 * l1) + l * (k0 * l1 + l0 * k1) = (k * k0 + l * l0) * k1 + (k * l0 + l * k0) * l1).
intros.
rewrite n_distributive with (n:=k). rewrite n_distributive with (n:=l).
rewrite n_mul_assoc. rewrite n_mul_assoc. rewrite n_mul_assoc with (n:=l).
rewrite n_plus_assoc. rewrite n_plus_comm.
rewrite n_mul_comm with (m:=l1). rewrite n_mul_comm with (m:=l1). 
rewrite <- n_plus_assoc. rewrite <- n_distributive with (n:=l1). rewrite n_mul_comm with (n:=l1).
rewrite n_plus_assoc. rewrite n_mul_assoc with (k:=k1).
rewrite n_mul_comm with (m:=k1). rewrite n_mul_comm with (m:=k1).
rewrite <- n_distributive with (n:=k1). rewrite n_mul_comm with (n:=k1).
rewrite n_plus_comm with (n:=l*l0). reflexivity.

rewrite H. rewrite H with (k:=n)(l:=m). reflexivity.
Qed.





