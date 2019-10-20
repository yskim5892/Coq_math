Require Import Logic_utils.
Require Import Relation.
Require Import Ordering.
Require Import NatProps.

Inductive Z : Type :=
  | z ( n m : nat).

Axiom z_eq : forall (n0 n1 m0 m1 : nat),
n0 + m1 = n1 + m0 <-> z n0 m0 = z n1 m1.

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
{ intros.
rewrite n_distributive with (n:=k). rewrite n_distributive with (n:=l).
set (a:=k*k0). set (b:=k*k1). set (c:=l*l0). set (d:=l*l1).
rewrite n_plus_assoc. rewrite <- n_plus_assoc with (k:=c). rewrite n_plus_comm with (n:=b).
rewrite n_plus_assoc. rewrite <- n_plus_assoc with (k:=d). reflexivity. }
rewrite H. rewrite H with (k:=n)(l:=m). reflexivity.
Qed.

Theorem z_mul_assoc : forall (a b c : Z),
  z_mul a (z_mul b c) = z_mul(z_mul a b) c.
Proof.
intros. destruct a, b, c. simpl.
assert (H : forall (k k0 k1 l l0 l1: nat), 
  k * (k0 * k1 + l0 * l1) + l * (k0 * l1 + l0 * k1) = (k * k0 + l * l0) * k1 + (k * l0 + l * k0) * l1).
intros.
{ rewrite n_distributive with (n:=k). rewrite n_distributive with (n:=l).
rewrite n_right_distributive with (k:=k1). rewrite n_right_distributive with (k:=l1).
rewrite n_mul_assoc. set (a:=k*k0*k1).
rewrite n_mul_assoc. set (b:=k*l0*l1).
rewrite n_mul_assoc. set (c:=l*k0*l1).
rewrite n_mul_assoc. set (d:=l*l0*k1).
rewrite <- n_plus_assoc with (k:=b+c). rewrite n_plus_comm with (n:=d).
rewrite <- n_plus_assoc with (n:=a). rewrite n_plus_assoc with (n:=b).
reflexivity. }
rewrite H. rewrite H with (k:=n)(l:=m). reflexivity.
Qed.

(* inequality *)

Definition z_le : Relation Z Z :=
fun p => match p with
| (a, b) => ( match a with
  | z n0 m0 => match b with
    | z n1 m1 => n0 + m1 <= n1 + m0
    end
  end)
end.

Definition z_lt : Relation Z Z :=
fun p => match p with
| (a, b) => ( match a with
  | z n0 m0 => match b with
    | z n1 m1 => n0 + m1 < n1 + m0
    end
  end)
end.

Definition z_ge : Relation Z Z :=
fun p => match p with
| (a, b) => z_le (b, a)
end.

Definition z_gt : Relation Z Z :=
fun p => match p with
| (a, b) => z_lt (b, a)
end.

Theorem z_le_reflexive : forall (a : Z),
  z_le(a, a).
Proof.
destruct a. simpl. apply le_n.
Qed.

Theorem z_le_transitive : forall (a b c : Z),
  z_le(a, b) /\ z_le(b, c) -> z_le(a, c).
Proof.
destruct a, b, c. simpl. intros.
apply n_le_sum in H.
rewrite n_plus_comm in H. rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
apply n_le_plus in H.
rewrite <- n_plus_assoc in H. rewrite <- n_plus_assoc in H.
rewrite n_plus_comm in H. rewrite n_plus_comm with (n:=n0) in H.
apply n_le_plus in H.
rewrite n_plus_comm. rewrite n_plus_comm with (n:=n1). apply H.
Qed.

Theorem z_le_antisymmetric : forall (a b : Z),
  z_le(a, b) /\ z_le(b, a) -> a = b.
Proof.
destruct a, b. simpl. intros.
apply n_le_antisymmetric in H. apply z_eq.
apply H.
Qed.

Theorem z_le_total_ordering : forall (a b : Z),
  z_le(a, b) \/ z_le(b, a).
Proof.
intros. destruct a, b. simpl.
apply n_le_total_partial_ordering.
Qed.

Theorem z_le_total_partial_ordering : total_partial_ordering z_le.
Proof.
unfold total_partial_ordering. apply conj.
- unfold partial_ordering. apply conj.
  + unfold reflexive. apply z_le_reflexive.
  + apply conj.
    * unfold antisymmetric. apply z_le_antisymmetric.
    * unfold transitive. apply z_le_transitive.
- apply z_le_total_ordering.
Qed.

Theorem z_lt_is_strict_z_le : z_lt = partial_to_strict z_le.
Proof.
assert (nl : forall (n m: nat), n_lt (n, m) <-> partial_to_strict n_le (n, m)).
{ apply Relation_eq. apply n_lt_is_strict_n_le. }
unfold partial_to_strict in nl.

apply Relation_eq. intros. unfold partial_to_strict.
destruct a, b.
unfold z_lt, z_le.
assert (zneq : z n m <> z n0 m0 <-> n + m0 <> n0 + m).
{ apply not_iff_compat. apply iff_sym. apply z_eq. }
apply and_iff_compat_l with (A:=n+m0<=n0+m) in zneq.
apply iff_iff_compat_l with (A:=n+m0<n0+m) in zneq.
apply zneq. apply nl.
Qed.

Theorem z_le_is_partial_z_lt : z_le = strict_to_partial z_lt.
Proof.
rewrite z_lt_is_strict_z_le. apply eq_sym.
apply partial_to_strict_to_partial_identity.
apply z_le_total_partial_ordering.
Qed.

Theorem z_lt_total_strict_ordering : total_strict_ordering z_lt.
Proof.
rewrite z_lt_is_strict_z_le.
apply partial_to_strict_preserves_totality.
apply z_le_total_partial_ordering.
Qed.

Theorem z_le_plus : forall (a b c : Z),
  z_le(a, b) -> z_le ((z_plus a c), (z_plus b c)).
Proof.
destruct a, b, c. simpl. intros.
rewrite n_plus_assoc. rewrite n_plus_assoc.
apply n_le_plus.
rewrite <- n_plus_assoc. rewrite <- n_plus_assoc.
rewrite n_plus_comm with (n:=n1). rewrite n_plus_comm with (n:=n1).
rewrite n_plus_assoc. rewrite n_plus_assoc.
apply n_le_plus. apply H.
Qed.
