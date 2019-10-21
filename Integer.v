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
Notation "-z a" := (z_neg a) (at level 35, right associativity).

Theorem z_eq_neg : forall (a b : Z),
  -za = -zb -> a = b.
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
  a +z -za = z_0.
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
  a +z c = b +z c -> a = b.
Proof.
intros. destruct a, b, c. simpl in H. apply z_eq in H. apply z_eq.
rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
apply n_plus_cancel in H.
rewrite <- n_plus_assoc in H. rewrite <- n_plus_assoc in H.
rewrite n_plus_comm with (n:=n1) in H. rewrite n_plus_comm with (n:=n1) in H.
rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
apply n_plus_cancel in H. apply H.
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
  a *z (-zb) = -z(a *z b).
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
  a <=z b -> b <=z c -> a <=z c.
Proof.
destruct a, b, c. simpl. intros ab bc.
pose (H:=n_le_sum (n+m0) (n0+m) (n0+m1) (n1+m0) ab bc).
rewrite n_plus_comm in H. rewrite n_plus_assoc in H. rewrite n_plus_assoc in H.
apply n_le_plus in H.
rewrite <- n_plus_assoc in H. rewrite <- n_plus_assoc in H.
rewrite n_plus_comm in H. rewrite n_plus_comm with (n:=n0) in H.
apply n_le_plus in H.
rewrite n_plus_comm. rewrite n_plus_comm with (n:=n1). apply H.
Qed.

Theorem z_le_antisymmetric : forall (a b : Z),
  a <=z b -> b <=z a -> a = b.
Proof.
destruct a, b. simpl. intros ab ba.
apply n_le_antisymmetric in ba. apply z_eq. apply ba. apply ab.
Qed.

Theorem z_le_total_ordering : forall (a b : Z),
  a <=z b \/ b <=z a.
Proof.
intros. destruct a, b. simpl. apply n_le_total_partial_ordering.
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

apply Relation_eq. intros. unfold partial_to_strict.
destruct a, b.
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
  a <=z b -> -zb <=z -za.
Proof.
  destruct a, b. simpl. intros.
  rewrite n_plus_comm. rewrite n_plus_comm with (n:=m). apply H.
Qed.

Theorem z_lt_neg : forall (a b : Z),
  a <z b -> -zb <z -za.
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
  a <=z b -> c <=z d -> a +z c <=z b +z d.
Proof.
destruct a, b, c, d. simpl. intros ab cd.
pose (H:=n_le_sum (n+m0) (n0+m) (n1+m2) (n2+m1) ab cd).
rewrite <- n_plus_assoc. rewrite <- n_plus_assoc.
rewrite n_plus_assoc with (n:=n1). rewrite n_plus_assoc with (n:=n2).
rewrite n_plus_comm with (n:=n1). rewrite n_plus_comm with (n:=n2).
rewrite <- n_plus_assoc. rewrite <- n_plus_assoc.
rewrite n_plus_assoc. rewrite n_plus_assoc with (n:=n0). apply H.
Qed.

Theorem z_lt_plus : forall (a b c : Z),
  a <z b <-> a +z c <z b +z c.
Proof.
intros. apply conj.
- rewrite z_lt_is_strict_z_le. intros ab. apply conj.
  + apply z_le_plus. apply ab.
  + intros eqacbc. apply z_plus_cancel in eqacbc. apply ab in eqacbc. contradiction.
- rewrite z_lt_is_strict_z_le. intros acbc. apply conj.
  + apply proj1 in acbc. apply z_le_plus in acbc. apply acbc.
  + intros eqab. rewrite eqab in acbc. apply acbc. reflexivity.
Qed.

Theorem z_le_lt_sum : forall (a b c d : Z),
  a <z b -> c <=z d -> a +z c <z b +z d.
Proof.
intros a b c d ab cd.
rewrite z_lt_is_strict_z_le in ab. rewrite z_lt_is_strict_z_le. apply conj.
- apply z_le_sum. apply ab. apply cd.
- intros ac_eq_bd. apply z_le_plus with (c:=a) in cd. rewrite z_plus_comm in cd. rewrite z_plus_comm with (a:=d) in cd.
  rewrite ac_eq_bd in cd. apply z_le_plus in cd. 
  pose (leH := z_le_total_partial_ordering). destruct leH as [partial total].
  destruct partial as [refl anti]. apply proj1 in anti.
  destruct ab as [ab a_neq_b]. apply a_neq_b in anti. contradiction.
  apply ab. apply cd.
Qed.

Theorem z_lt_sum : forall (a b c d : Z),
  a <z b -> c <z d -> a +z c <z b +z d.
Proof.
intros a b c d ab cd.
rewrite z_lt_is_strict_z_le in cd. apply z_le_lt_sum. apply ab. apply cd.
Qed.

Theorem z_lt_mul : forall (a b c : Z),
  a <z b -> z_0 <z c -> a *z c <z b *z c.
Proof.
destruct a, b, c. simpl. intros ab cpos. rewrite n_plus_identity in cpos.
rewrite <- n_plus_assoc. rewrite n_plus_assoc with (n:=m*m1). 
rewrite <- n_right_distributive. rewrite n_plus_comm with (m:=m0*n1).
rewrite n_plus_assoc. rewrite <- n_right_distributive. rewrite n_plus_comm with (n:=m).

rewrite <- n_plus_assoc. rewrite n_plus_assoc with (n:=m0*m1).
rewrite <- n_right_distributive. rewrite n_plus_comm with (m:=m*n1).
rewrite n_plus_assoc. rewrite <- n_right_distributive. rewrite n_plus_comm with (m:=n).
rewrite n_plus_comm with (n:=(n0+m)*n1).

apply n_lt_lemma1. apply ab. apply cpos.
Qed.

Theorem z_lt_mul2 : forall (a b c : Z),
  a *z c <z b *z c -> z_0 <z c -> a <z b.
Proof.
intros a b c acbc cpos.
destruct z_lt_total_strict_ordering as [strict total].
destruct (total a b) as [ab|ba].
- apply ab.
- destruct ba as [ba|eq].
  + pose (bcac := z_lt_mul b a c ba cpos). apply strict in bcac. contradiction.
  + rewrite eq in acbc. apply strict in acbc as bcac. contradiction.
Qed. 

Theorem z_le_mul : forall (a b c : Z),
  a <=z b -> z_0 <=z c -> a *z c <=z b *z c.
Proof.
intros a b c ab cpos.
rewrite z_le_is_partial_z_lt in ab. destruct ab as [ab|eqab].
- rewrite z_le_is_partial_z_lt in cpos. destruct cpos as [cpos|c0].
  + rewrite z_le_is_partial_z_lt. left. apply z_lt_mul. apply ab. apply cpos.
  + rewrite <- c0. rewrite z_mul_zero. rewrite z_mul_zero. simpl. apply le_n.
- rewrite eqab. apply z_le_total_partial_ordering.
Qed.

Theorem z_le_mul2 : forall (a b c : Z),
  a *z c <=z b *z c -> z_0 <z c -> a <=z b.
Proof.
intros a b c acbc cpos.
destruct z_lt_total_strict_ordering as [strict total].
destruct (total a b) as [ab|ba].
- rewrite z_lt_is_strict_z_le in ab. apply ab.
- destruct ba as [ba|eq].
  + pose (bcac := z_lt_mul b a c ba cpos).
    rewrite z_lt_is_strict_z_le in bcac. destruct bcac.
    apply z_le_total_partial_ordering in acbc. apply acbc in H. apply eq_sym in H. contradiction.
  + rewrite eq. apply z_le_total_partial_ordering.
Qed.

Theorem z_pos_nonzero : forall (a : Z),
  z_0 <z a -> a <> z_0.
Proof.
intros. intro. rewrite H0 in H. inversion H.
Qed.

Theorem z_mul_cancel : forall (a b c : Z),
  a *z c = b *z c /\ ~ c = z_0 -> a = b.
Proof.
intros a b c. 
pose z_lt_total_strict_ordering as H. destruct H as [strict total].
intros eqacbc. destruct (total z_0 c) as [c_pos|c_neg].
- apply proj1 in eqacbc. destruct (total a b) as [ab|ba].
  + pose (acbc:= z_lt_mul a b c ab c_pos). rewrite eqacbc in acbc.
    apply z_lt_total_strict_ordering in acbc as bcac. contradiction.
  + destruct ba as [ba|eqab]. 
    * pose (bcac:= z_lt_mul b a c ba c_pos). rewrite eqacbc in bcac.
      apply z_lt_total_strict_ordering in bcac as acbc. contradiction.
    * apply eqab. 
- destruct c_neg as [c_neg|c0].
  + apply proj1 in eqacbc. set (nc := z_neg c). apply z_lt_neg in c_neg. simpl z_neg in c_neg.
    replace c with (z_neg (z_neg c)) in eqacbc.
    rewrite z_mul_neg in eqacbc. rewrite z_mul_neg with (a:=b) in eqacbc.
    apply z_eq_neg in eqacbc.
    destruct (total a b) as [ab|ba].
    * pose (acbc:= z_lt_mul a b (-z c) ab c_neg). rewrite eqacbc in acbc.
      apply z_lt_total_strict_ordering in acbc as bcac. contradiction.
    * destruct ba as [ba|eqab]. 
      --  pose (bcac:= z_lt_mul b a (-z c) ba c_neg). rewrite eqacbc in bcac.
          apply z_lt_total_strict_ordering in bcac as acbc. contradiction.
      -- apply eqab.
    * destruct c. reflexivity.
  + apply proj2 in eqacbc. apply eq_sym in c0. contradiction.
Qed.

Theorem z_mul_a_b_zero : forall (a b : Z),
  a *z b = z_0 <-> a = z_0 \/ b = z_0.
Proof.
intros. unfold iff. apply conj. 
- destruct (law_of_excluded_middle (b=z_0)).
  + right. apply H.
  + left. apply z_mul_cancel with (c:=b). apply conj.
    * rewrite H0. rewrite z_mul_comm. rewrite z_mul_zero. reflexivity.
    * apply H.
- intros. destruct H as [a0|b0].
  + rewrite a0. destruct b. apply z_eq. reflexivity.
  + rewrite b0. destruct a. apply z_eq. rewrite n_mul_zero. rewrite n_mul_zero. reflexivity.
Qed.

Theorem z_mul_a_b_nonzero : forall (a b : Z),
  a <> z_0 -> b <> z_0 -> a *z b <> z_0.
Proof.
intros a b an0 bn0. intros ab0. apply z_mul_a_b_zero in ab0. destruct ab0 as [a0|b0].
apply an0 in a0. contradiction. apply bn0 in b0. contradiction.
Qed.

Theorem z_mul_a_b_nonzero2 : forall (a b : Z),
  a *z b <> z_0 -> a <> z_0 /\ b <> z_0.
Proof.
intros. apply conj.
- intro. rewrite H0 in H. destruct b. simpl in H. contradiction.
- intro. rewrite H0 in H. destruct a. rewrite z_mul_comm in H. simpl in H. contradiction.
Qed.