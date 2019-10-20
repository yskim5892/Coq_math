Theorem pair_eq : forall (A B: Type)(a a': A)(b b': B),
(a, b) = (a', b') <-> a = a' /\ b = b'.
Proof.
unfold iff. intros. apply conj.
- intros. injection H. intros. apply conj. apply H1. apply H0.
- intros. apply proj1 in H as H1. apply proj2 in H as H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Definition Relation (A B : Type) : Type := (prod A B -> Prop).

Axiom Relation_eq : forall {A B} (R S : Relation A B),
(forall (a:A)(b:B), R(a, b) <-> S(a, b)) <-> R = S.

Definition dom {A B}(R : Relation A B) : (A -> Prop) := 
(fun x => (exists y:B, R(x, y))).

Definition ran {A B}(R : Relation A B) : (B -> Prop) :=
(fun y => (exists x:A, R(x, y))).

Definition image {A B}(R : Relation A B) : ((A -> Prop) -> (B -> Prop)) :=
(fun A_ => (fun y => (exists x:A, A_ x -> R(x, y)))).

Definition inv_image {A B}(R : Relation A B) : ((B -> Prop) -> (A -> Prop)) :=
(fun B_ => (fun x => (exists y:B, B_ y -> R(x, y)))).

Definition inv {A B}(R : Relation A B) : Relation B A :=
(fun p => (match p with 
  | (b,a) => R(a, b) 
end)).

Definition composition {A B C} (R : Relation A B) (S : Relation B C) : Relation A C :=
(fun p => (match p with
  | (a, c) => exists b, R(a, b) /\ S(b, c)
end)).

Definition symmetric {A} (R : Relation A A) : Prop :=
forall (a b : A), R(a, b) -> R(b, a).

Definition antisymmetric {A} (R : Relation A A) : Prop :=
forall (a b : A), R(a, b) /\ R(b, a) -> a = b.

Definition asymmetric {A} (R: Relation A A) : Prop :=
forall (a b : A), R(a, b) -> not (R(b, a)).

Definition transitive {A} (R: Relation A A) : Prop :=
forall (a b c : A), R(a, b) /\ R(b, c) -> R(a, c).

Definition reflexive {A} (R : Relation A A) : Prop :=
forall (a : A), R(a, a).

Definition injective {A B} (R : Relation A B) : Prop :=
forall (a1 a2 : A)(b : B), R(a1, b) /\ R(a2, b) -> a1 = a2.

Definition functional {A B} (R : Relation A B) : Prop :=
forall (a : A)(b1 b2 : B), R(a, b1) /\ R(a, b2) -> b1 = b2.

Definition one_to_one {A B} (R : Relation A B) : Prop :=
injective R /\ functional R.

Definition left_total {A B} (R : Relation A B) : Prop :=
forall (a : A), exists (b : B), R(a, b).

Definition surjective {A B} (R : Relation A B) : Prop :=
forall (b : B), exists (a : A), R(a, b).

Definition equiv {A} (R : Relation A A) : Prop :=
reflexive R /\ transitive R /\ symmetric R.

