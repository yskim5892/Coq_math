Parameter set : Type.
Parameter In : set -> set -> Prop.

Notation "x ∈ y" := (In x y) (at level 30).
Notation "x ∋ y" := (In y x) (at level 30).

Definition subset (A B: set) : Prop :=
forall x:set, x ∈ A -> x ∈ B.

Notation "x ⊆ y" := (subset x y) (at level 30).
Notation "x ⊇ y" := (subset y x) (at level 30).

Theorem subset_reflexive : forall (A : set),
A ⊆ A.
Proof.
intros. unfold subset. intros.
apply H.
Qed.

Theorem subset_transitive : forall (A B C : set),
A ⊆ B /\ B ⊆ C -> A ⊆ C.
Proof.
intros A B C. unfold subset. intros.
inversion H. apply H2. apply H1. apply H0.
Qed.

Parameter Φ : set.
Axiom Axiom_of_Existence :
forall x:set, not (x ∈ Φ).

Axiom Axiom_of_Extensionality :
forall (A B : set), (forall x:set, x ∈ A <-> x ∈ B) -> A = B.

Theorem subset_antisymmetric : forall (A B : set),
A ⊆ B /\ B ⊆ A -> A = B.
Proof.
intros. apply Axiom_of_Extensionality. 
inversion H. unfold subset in H0. unfold subset in H1.
intros x. unfold iff. apply conj. apply H0. apply H1.
Qed.

Axiom Axiom_of_Regularity : forall A : set,
(exists B :set, B ∈ A) -> (exists B : set, B ∈ A /\ not (exists C : set, C ∈ A /\ C ∈ B)).

Axiom Axiom_of_Pairing : forall (A B : set),
exists C, A ∈ C /\ B ∈ C.

Axiom Axiom_of_Union : forall (A : set),
exists U, forall (x y: set), x ∈ y /\ y ∈ A -> x ∈ U.

Axiom Axiom_of_Powerset : forall (A : set),
exists B, forall (x : set), x ⊆ A -> x ∈ B.
