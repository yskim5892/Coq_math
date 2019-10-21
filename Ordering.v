Require Import Relation.
Require Import Logic_utils.

Definition partial_ordering {A} (R : Relation A A) : Prop :=
reflexive R /\ antisymmetric R /\ transitive R.

Definition strict_ordering {A} (R : Relation A A) : Prop :=
asymmetric R /\ transitive R.

Definition partial_to_strict {A} (R : Relation A A) : Relation A A :=
fun p => match p with
  | (a, b) => R(a, b) /\ a <> b
end.

Definition strict_to_partial {A} (S: Relation A A) : Relation A A :=
fun p => match p with
  | (a, b) => S(a, b) \/ a = b
end.

Theorem partial_to_strict_returns_strict : 
forall (A: Type)(R: Relation A A), partial_ordering R -> strict_ordering (partial_to_strict R).
Proof.
intros. set (S:=partial_to_strict R).
destruct H as [refl anti]. destruct anti as [anti trans].
apply conj.
- intros a b Sab. intros Sba.
  apply Sba in anti. contradiction. apply Sba. apply Sab.
- intros a b c Sab Sbc. apply conj.
  + apply trans with (b:=b). apply Sab. apply Sbc.
  + intros ac. rewrite <- ac in Sbc.
    apply Sab in anti. contradiction. apply Sab. apply Sbc.
Qed.

Theorem strict_to_partial_returns_partial :
forall (A:Type)(S: Relation A A), strict_ordering S -> partial_ordering (strict_to_partial S).
Proof.
intros. set (R:=strict_to_partial S).
destruct H as [asymm trans].
apply conj.
- unfold reflexive. intros. right. reflexivity.
- apply conj.
  + unfold antisymmetric. intros a b Rab Rba.
    destruct Rab as [Sab|eq1]. destruct Rba as [Sba|eq2].
    * apply asymm in Sba. contradiction.
    * rewrite eq2. reflexivity.
    * rewrite eq1. reflexivity.
  + unfold transitive. intros a b c Rab Rbc.
    destruct Rab as [Sab|eq1]. destruct Rbc as [Sbc|eq2].
    * left. apply trans with (b:=b). apply Sab. apply Sbc.
    * left. rewrite <- eq2. apply Sab.
    * rewrite eq1. apply Rbc.
Qed.

Definition total_partial_ordering {A} (R : Relation A A) : Prop :=
  partial_ordering R /\ forall (a b : A), R(a, b) \/ R(b, a).

Definition total_strict_ordering {A} (S : Relation A A) : Prop :=
  strict_ordering S /\ forall (a b : A), S(a, b) \/ S(b, a) \/ a = b.

Theorem partial_to_strict_preserves_totality : 
forall (A: Type)(R : Relation A A), 
total_partial_ordering R -> total_strict_ordering (partial_to_strict R).
Proof.
intros. set (S:=partial_to_strict R).
destruct H as [partialR totalR]. 
apply conj. 
- apply partial_to_strict_returns_strict. apply partialR.
- intros. 
  assert (eq : (a=b) \/ (a <> b)).
  { apply law_of_excluded_middle. }
  destruct (totalR a b) as [Rab|Rba].
  + destruct eq as [eq|neq].
    * right. right. apply eq.
    * left. apply conj. apply Rab. apply neq.
  + destruct eq as [eq|neq].
    * right. right. apply eq.
    * right. left. apply conj. apply Rba. apply (neq_comm A). apply neq.
Qed.

Theorem struct_to_partial_preserves_totality :
forall (A: Type)(S : Relation A A),
total_strict_ordering S -> total_partial_ordering (strict_to_partial S).
Proof.
intros. set (R:=strict_to_partial S).
destruct H as [strictS totalS].
apply conj.
- apply strict_to_partial_returns_partial. apply strictS.
- intros. destruct (totalS a b) as [Sab|Rba].
  + left. left. apply Sab.
  + destruct Rba as [Sba|eq].
    * right. left. apply Sba. 
    * left. right. apply eq.
Qed.

Theorem strict_to_partial_to_strict_identity :
forall (A: Type)(S : Relation A A),
strict_ordering S -> partial_to_strict (strict_to_partial S) = S.
Proof.
intros. set (R:= strict_to_partial S). set (S':= partial_to_strict R).
apply Relation_eq. intros.
unfold iff. apply conj.
- intros S'ab. apply reduce_or_P_and_notP in S'ab. apply S'ab.
- intros Sab. apply conj.
  + left. apply Sab.
  + destruct H as [asymm trans]. intros eq. destruct (asymm a b).
    * apply Sab.
    * rewrite eq. rewrite eq in Sab. apply Sab.
Qed.

Theorem partial_to_strict_to_partial_identity :
forall (A: Type)(R : Relation A A),
partial_ordering R -> strict_to_partial (partial_to_strict R) = R.
Proof.
intros. set (S:= partial_to_strict R). set (R':= strict_to_partial S).
apply Relation_eq. intros.
unfold iff. apply conj.
- intros R'ab. inversion R'ab.
  + apply H0.
  + destruct H as [refl _]. rewrite H0. apply refl.
- intros Rab. 
  assert (eq: (a=b) \/ (a<>b)).
  { apply law_of_excluded_middle. }
  destruct eq as [eq|neq].
  + right. apply eq.
  + left. split. apply Rab. apply neq.
Qed.