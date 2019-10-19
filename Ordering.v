Require Import Relation.

Definition partial_ordering {A} (R : Relation A A) : Prop :=
reflexive R /\ antisymmetric R /\ transitive R.

Definition strict_ordering {A} (R : Relation A A) : Prop :=
asymmetric R /\ transitive R.

Definition partial_to_strict {A} (R : Relation A A) : Relation A A :=
fun p => match p with
  | (a, b) => R(a, b) /\ a <> b
end.

Definition strict_to_partial {A} (R: Relation A A) : Relation A A :=
fun p => match p with
  | (a, b) => R(a, b) \/ a = b
end.

Theorem strict_to_partial_returns_strict : 
forall (A: Type)(R: Relation A A), partial_ordering R -> strict_ordering (partial_to_strict R).
Proof.
intros.
apply conj.
- set (S:=partial_to_strict R). unfold asymmetric.
  intros a b Sab.
  unfold partial_to_strict in S. intros Sba.
  unfold S in Sab. unfold S in Sba.
  apply proj1 in Sab as Rab. apply proj1 in Sba as Rba. apply proj2 in Sba as a_neq_b.
  
  inversion H. inversion H1. unfold antisymmetric in H2.
  apply a_neq_b in H2.
  + apply H2.
  + apply conj. apply Rba. apply Rab.
- set (S:=partial_to_strict R). unfold transitive.
  intros a b c SabSbc.
  unfold partial_to_strict in S.
  apply proj1 in SabSbc as Sab. apply proj2 in SabSbc as Sbc.
  unfold S in Sab. unfold S in Sbc. unfold S.
  apply conj.
  + apply proj1 in Sbc. apply proj1 in Sab.
    inversion H. inversion H1. unfold transitive in H3.
    apply H3 with (b:=b).
    apply conj. apply Sab. apply Sbc.
  + intros a_eq_c. rewrite <- a_eq_c in Sbc. 
    apply proj1 in Sab as Rab. apply proj1 in Sbc as Rba. apply proj2 in Sab as a_neq_b.
    inversion H. inversion H1. unfold antisymmetric in H2.
    apply a_neq_b in H2.
    * apply H2.
    * apply conj. apply Rab. apply Rba.
Qed.

Theorem partial_to_strict_returns_partial :
forall (A:Type)(S: Relation A A), strict_ordering S -> partial_ordering (strict_to_partial S).
Proof.
intros.
apply conj.
- unfold reflexive. unfold strict_to_partial. intros.
  apply or_intror. reflexivity.
- apply conj.
  + set (R:=strict_to_partial S). unfold antisymmetric.
    intros a b RabRba.
    apply proj1 in RabRba as Rab. apply proj2 in RabRba as Rba.
    unfold strict_to_partial in R.
    unfold R in Rab. destruct Rab as [Sab|eq1].
    unfold R in Rba. destruct Rba as [Sba|eq2].
    * unfold strict_ordering in H. apply proj1 in H as asymm.
      unfold asymmetric in asymm. apply asymm in Sba. apply Sba in Sab. destruct Sab.
    * rewrite eq2. reflexivity.
    * rewrite eq1. reflexivity.
  + set (R:=strict_to_partial S). unfold transitive.
    intros a b c RabRbc.
    apply proj1 in RabRbc as Rab. apply proj2 in RabRbc as Rbc.
    unfold strict_to_partial in R.
    unfold R.
    unfold R in Rab. destruct Rab as [Sab|eq1].
    unfold R in Rbc. destruct Rbc as [Sbc|eq2].
    * unfold strict_ordering in H. apply proj2 in H as trans.
      unfold transitive in trans. apply or_introl.
      apply trans with (b:=b). apply conj. apply Sab. apply Sbc.
    * apply or_introl. rewrite <- eq2. apply Sab.
    * destruct Rbc as [Sbc|eq2].
      -- apply or_introl. rewrite eq1. apply Sbc. 
      -- apply or_intror. rewrite eq1. rewrite eq2. reflexivity.
Qed.

Definition total_partial_ordering {A} (R : Relation A A) : Prop :=
  partial_ordering R /\ forall (a b : A), R(a, b) \/ R(b, a).

Definition total_strict_ordering {A} (S : Relation A A) : Prop :=
  strict_ordering S /\ forall (a b : A), S(a, b) \/ S(b, a) \/ a = b.



