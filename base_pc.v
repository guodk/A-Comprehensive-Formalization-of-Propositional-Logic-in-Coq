Require Import Coq.Sets.Ensembles.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a) (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).

Inductive Formula : Type:=
  | Var : nat -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula.

Notation "¬ q" := (Not q)(at level 5,right associativity).
Notation "p → q" := (Contain p q)(at level 8,right associativity).

Corollary UnionI : forall {U} (a:U) B C, a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. split; intros; destruct H; eauto with sets. Qed.

Corollary Single : forall {U} (a x:U), a ∈ [ x ] -> a = x.
Proof. intros; destruct H; auto. Qed.

Global Hint Resolve UnionI Single: sets.

Definition Φ := @Empty_set Formula.
Ltac ES := 
  match goal with
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?p0 ∈ [?p] |- _ => apply Single in H; rewrite H in *; ES
  | H: ?a ∈ (?B ∪ ?C) |- _ => apply UnionI in H; ES
  | |- ?a ∈ (?B ∪ ?C) => apply UnionI; ES
  | H: ?B \/ ?C |- _ => destruct H; ES
  | H: ?B /\ ?C |- _ => destruct H; ES
  | |- forall a, ?Q => intros; ES
  | |- ?P <-> ?Q => split; intros; ES
  | |- _ => eauto with sets
  end.
