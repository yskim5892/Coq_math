Theorem pair_eq : forall (A B: Type)(a a': A)(b b': B),
(a, b) = (a', b') <-> a = a' /\ b = b'.
Proof.
unfold iff. intros. apply conj.
- intros. injection H. intros. apply conj. apply H1. apply H0.
- intros. apply proj1 in H as H1. apply proj2 in H as H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Print pair.
Definition Relation (A B : Type) : Type := (prod A B -> Prop).

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