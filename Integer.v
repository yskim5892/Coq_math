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
Notation "a +z b" := (z_plus a b) (at level 50, left associativity).
Notation "a -z b" := (z_minus a b) (at level 50, left associativity).
Notation "a *z b" := (z_mul a b) (at level 40, left associativity).
Notation "- a" := (z_neg a) (at level 35, right associativity).

Theorem z_eq_neg : forall (a b : Z),
  -a = -b -> a = b.
Proof.
destruct a, b. simpl. intros. apply z_eq in H. apply z_eq.
rewrite n_plus_comm. rewrite n_plus_comm with (m:=m). rewrite H. reflexivity.
Qed.

Theorem z_plus_identity : forall (a : Z),
  a +z z_0 = a.
Proof.
intros. destruct a. simpl. rewrite n_plus_identity. rewrite n_plus_identity with (n:=m). reflexivity.
Qed.

Theorem z_plus_inverse : forall (a : Z),
  a +z -a = z_0.
Proof.
destruct a. simpl. apply z_eq. 
rewrite n_plus_identity. simpl. apply n_plus_comm.
Qed.

Theorem z_plus_comm : forall (a b : Z),
  a +z b = b +z a.
Proof.
destruct a, b. simpl. rewrite n_plus_comm. rewrite n_plus_comm with (n:=m0). reflexivity. 
Qed.

Theorem z_plus_assoc : forall (a b c : Z),
  (a +z b) +z c = a +z (b +z c).
Proof.
destruct a, b, c. simpl. rewrite n_plus_assoc. rewrite n_plus_assoc with (n:=m). reflexivity.
Qed.

Theorem z_plus_cancel : forall (a b c : Z),
  a +z c = b +z c <-> a = b.
Proof.
intros. unfold iff. apply conj.
- intros. destruct a, b, c. simpl in H. apply z_eq in H. apply z_eq.
  rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
  apply n_plus_cancel in H.
  rewrite <- n_plus_assoc in H. rewrite <- n_plus_assoc in H.
  rewrite n_plus_comm with (n:=n1) in H. rewrite n_plus_comm with (n:=n1) in H.
  rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
  apply n_plus_cancel in H. apply H.
- intros. rewrite H. reflexivity.
Qed.

Theorem z_mul_identity : forall (a : Z),
  a *z z_1 = a.
Proof.
destruct a. simpl. 
rewrite n_mul_identity. rewrite n_mul_identity with (n:=m).
rewrite n_mul_zero. rewrite n_mul_zero. simpl.
rewrite n_plus_identity. reflexivity.
Qed.

Theorem z_mul_zero : forall (a : Z),
  a *z z_0 = z_0.
Proof.
destruct a. simpl. 
rewrite n_mul_zero. rewrite n_mul_zero.
rewrite n_plus_identity. reflexivity.
Qed.

Theorem z_mul_neg : forall (a b : Z),
  a *z (-b) = -(a *z b).
Proof.
destruct a, b. simpl. apply z_eq. reflexivity.
Qed.

Theorem z_mul_comm : forall (a b : Z),
  a *z b = b *z a.
Proof.
intros. destruct a, b. simpl.
rewrite n_mul_comm. rewrite n_mul_comm with(n:=m).
rewrite n_mul_comm with (m:=m0). rewrite n_mul_comm with (m:=n0). 
rewrite n_plus_comm with (n:=m0*n). reflexivity.
Qed.

Theorem z_distributive : forall (a b c : Z),
  a *z (b +z c) = a *z b +z a *z c.
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
  a *z (b *z c) = (a *z b) *z c.
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

Notation "a <=z b" := (z_le (a, b)) (at level 70, no associativity).
Notation "a <z b"  := (z_lt (a, b)) (at level 70, no associativity).
Notation "a >=z b" := (z_ge (a, b)) (at level 70, no associativity).
Notation "a >z b"  := (z_gt (a, b)) (at level 70, no associativity).

Theorem z_le_reflexive : forall (a : Z),
  a <=z a.
Proof.
destruct a. simpl. apply le_n.
Qed.

Theorem z_le_transitive : forall (a b c : Z),
  a <=z b /\ b <=z c -> a <=z c.
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
  a <=z b /\ b <=z a -> a = b.
Proof.
destruct a, b. simpl. intros.
apply n_le_antisymmetric in H. apply z_eq.
apply H.
Qed.

Theorem z_le_total_ordering : forall (a b : Z),
  a <=z b \/ b <=z a.
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

Theorem z_le_neg : forall (a b : Z),
  a <=z b -> -b <=z -a.
Proof.
  destruct a, b. simpl. intros.
  rewrite n_plus_comm. rewrite n_plus_comm with (n:=m). apply H.
Qed.

Theorem z_lt_neg : forall (a b : Z),
  a <z b -> -b <z -a.
Proof.
  destruct a, b. simpl. intros.
  rewrite n_plus_comm. rewrite n_plus_comm with (n:=m). apply H.
Qed.

Theorem z_le_plus : forall (a b c : Z),
  a <=z b <-> a +z c <=z b +z c.
Proof.
destruct a, b, c. simpl. unfold iff. apply conj.
- intros. rewrite n_plus_assoc. rewrite n_plus_assoc.
  apply n_le_plus.
  rewrite <- n_plus_assoc. rewrite <- n_plus_assoc.
  rewrite n_plus_comm with (n:=n1). rewrite n_plus_comm with (n:=n1).
  rewrite n_plus_assoc. rewrite n_plus_assoc.
  apply n_le_plus. apply H.
- intros. rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
  apply n_le_plus in H.
  rewrite <- n_plus_assoc in H. rewrite <- n_plus_assoc in H.
  rewrite n_plus_comm with (n:=n1) in H. rewrite n_plus_comm with (n:=n1) in H.
  rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
  apply n_le_plus in H. apply H.
Qed.

Theorem z_le_sum : forall (a b c d : Z),
  a <=z b /\ c <=z d -> a +z c <=z b +z d.
Proof.
destruct a, b, c, d. simpl. intros H.
apply n_le_sum in H. rewrite <- n_plus_assoc. rewrite <- n_plus_assoc.
rewrite n_plus_assoc with (n:=n1). rewrite n_plus_assoc with (n:=n2).
rewrite n_plus_comm with (n:=n1). rewrite n_plus_comm with (n:=n2).
rewrite <- n_plus_assoc. rewrite <- n_plus_assoc.
rewrite n_plus_assoc. rewrite n_plus_assoc with (n:=n0). apply H.
Qed.

Theorem z_lt_plus : forall (a b c : Z),
  a <z b <-> a +z c <z b +z c.
Proof.
intros. assert (ltH : forall (a' b': Z), z_lt (a', b') <-> partial_to_strict z_le (a', b')).
{ apply Relation_eq. apply z_lt_is_strict_z_le. }
unfold partial_to_strict in ltH.
unfold iff. apply conj.
- intros lab. apply ltH in lab. apply ltH. 
  apply conj.
  + apply proj1 in lab. apply z_le_plus. apply lab.
  + intros ac_eq_bc. apply z_plus_cancel in ac_eq_bc. apply lab in ac_eq_bc. contradiction.
- intros lacbc. apply ltH in lacbc. apply ltH.
  apply conj.
  + apply proj1 in lacbc. apply z_le_plus in lacbc. apply lacbc.
  + intros a_eq_b. rewrite a_eq_b in lacbc. apply lacbc. reflexivity.
Qed.

Theorem z_le_lt_sum : forall (a b c d : Z),
  a <z b /\ c <=z d -> a +z c <z b +z d.
Proof.
intros. assert (ltH : forall (a' b': Z), z_lt (a', b') <-> partial_to_strict z_le (a', b')).
{ apply Relation_eq. apply z_lt_is_strict_z_le. }
destruct H as [lab lcd]. apply ltH in lab. apply ltH. apply conj.
- apply proj1 in lab. apply z_le_sum. apply conj. apply lab. apply lcd.
- intros ac_eq_bd. apply z_le_plus with (c:=a) in lcd. rewrite z_plus_comm in lcd. rewrite z_plus_comm with (a:=d) in lcd.
  rewrite ac_eq_bd in lcd. apply z_le_plus in lcd. 
  pose (leH := z_le_total_partial_ordering). destruct leH as [partial total].
  destruct partial as [refl anti]. apply proj1 in anti.
  destruct lab as [lab a_neq_b]. apply a_neq_b in anti. contradiction.
  apply conj. apply lab. apply lcd.
Qed.

Theorem z_lt_sum : forall (a b c d : Z),
  a <z b /\ c <z d -> a +z c <z b +z d.
Proof.
intros. assert (ltH : forall (a' b': Z), z_lt (a', b') <-> partial_to_strict z_le (a', b')).
{ apply Relation_eq. apply z_lt_is_strict_z_le. }
destruct H as [lab lcd]. apply ltH in lcd.
apply z_le_lt_sum. apply conj. apply lab. apply lcd.
Qed.


Theorem z_lt_mul : forall (a b c : Z),
  a <z b /\ z_0 <z c -> a *z c <z b *z c.
Proof.
destruct a, b, c. simpl. intros.
rewrite n_plus_identity in H.
rewrite <- n_plus_assoc. rewrite n_plus_assoc with (n:=m*m1). 
rewrite <- n_right_distributive. rewrite n_plus_comm with (m:=m0*n1).
rewrite n_plus_assoc. rewrite <- n_right_distributive. rewrite n_plus_comm with (n:=m).

rewrite <- n_plus_assoc. rewrite n_plus_assoc with (n:=m0*m1).
rewrite <- n_right_distributive. rewrite n_plus_comm with (m:=m*n1).
rewrite n_plus_assoc. rewrite <- n_right_distributive. rewrite n_plus_comm with (m:=n).
rewrite n_plus_comm with (n:=(n0+m)*n1).

apply n_lt_lemma1. apply H.
Qed.

Theorem z_le_mul : forall (a b c : Z),
  a <=z b /\ z_0 <=z c -> a *z c <=z b *z c.
Proof.
intros. assert (leH : forall (a' b': Z), z_le (a', b') <-> strict_to_partial z_lt (a', b')).
{ apply Relation_eq. apply z_le_is_partial_z_lt. } unfold strict_to_partial in leH.
destruct H as [lab l0c].
apply leH in lab. destruct lab as [lab|eqab].
- apply leH in l0c. destruct l0c as [l0c|c0].
  + apply leH. left. apply z_lt_mul. apply conj. apply lab. apply l0c.
  + rewrite <- c0. rewrite z_mul_zero. rewrite z_mul_zero. simpl. apply le_n.
- rewrite eqab. apply z_le_total_partial_ordering.
Qed.

Theorem z_mul_cancel : forall (a b c : Z),
  a *z c = b *z c /\ ~ c = z_0 -> a = b.
Proof.
intros a b c.
pose z_lt_total_strict_ordering as H.
destruct H as [strict total].
unfold strict_ordering in strict. apply proj1 in strict. unfold asymmetric in strict.
assert (lemma : forall (a' b' c' : Z), z_lt(a', b') /\ z_lt (z_0, c') -> not (z_mul a' c' = z_mul b' c')).
{ intros. apply z_lt_mul in H. intros acbc.
  rewrite acbc in H. apply strict in H as contr. contradiction. }

destruct (total z_0 c) as [c_pos|c_neg].
- intros ac_eq_bc. apply proj1 in ac_eq_bc.
  destruct (total a b) as [lab|lba].
  + apply (lemma a b c) in ac_eq_bc. contradiction.
    apply conj. apply lab. apply c_pos.
  + destruct lba as [lba|a_eq_b].
    * apply eq_sym in ac_eq_bc. apply (lemma b a c) in ac_eq_bc. contradiction.
      apply conj. apply lba. apply c_pos.
    * rewrite a_eq_b. reflexivity.
- destruct c_neg as [c_neg|c0].
  + intros ac_eq_bc. apply proj1 in ac_eq_bc.
    set (nc := z_neg c). apply z_lt_neg in c_neg. simpl z_neg in c_neg.
    replace c with (z_neg (z_neg c)) in ac_eq_bc.
    rewrite z_mul_neg in ac_eq_bc. rewrite z_mul_neg with (a:=b) in ac_eq_bc.
    apply z_eq_neg in ac_eq_bc. 
    destruct (total a b) as [lab|lba].
    * apply (lemma a b nc) in ac_eq_bc. contradiction.
      apply conj. apply lab. apply c_neg.
    * destruct lba as [lba|a_eq_b].
      --  apply eq_sym in ac_eq_bc. apply (lemma b a nc) in ac_eq_bc. contradiction.
          apply conj. apply lba. apply c_neg.
      --  apply a_eq_b.
    * destruct c. reflexivity. 
  + intros. apply proj2 in H. apply eq_sym in c0. contradiction.
Qed.

Theorem z_mul_a_b_zero : forall (a b : Z),
  a *z b = z_0 -> a = z_0 \/ b = z_0.
Proof.
intros. destruct (law_of_excluded_middle (b=z_0)).
- right. apply H0.
- left. apply z_mul_cancel with (c:=b). apply conj.
  + rewrite H. rewrite z_mul_comm. rewrite z_mul_zero. reflexivity.
  + apply H0.
Qed.