Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import syntax.
Require Import semantic.

Inductive deduce_N (Γ:Ensemble Formula):Formula -> Prop:=
  |DN0 : forall p, p∈Γ -> deduce_N Γ p
  |DN1 : forall p q, deduce_N (Γ ∪ [p]) q -> deduce_N Γ (p → q) 
  |DN2 : forall p q, deduce_N Γ p -> deduce_N Γ (p → q) -> deduce_N Γ q
  |DN3 : forall p q, deduce_N Γ p -> deduce_N Γ (p∨q)
  |DN4 : forall p q, deduce_N Γ p -> deduce_N Γ (q∨p)
  |DN5 : forall p q r, deduce_N Γ (p∨q) -> deduce_N Γ (p→r) ->
        deduce_N Γ  (q→r) -> deduce_N Γ r
  |DN6 : forall p q, deduce_N Γ p -> deduce_N Γ q -> deduce_N Γ (p∧q)
  |DN7 : forall p q, deduce_N Γ (p∧q) -> deduce_N Γ p
  |DN8 : forall p q, deduce_N Γ (p∧q) -> deduce_N Γ p
  |DN9 : forall p q, deduce_N Γ (p → q) -> deduce_N Γ (q → p) ->
        deduce_N Γ (p ↔ q)
  |DN10: forall p q, deduce_N Γ (p ↔ q) -> deduce_N Γ p -> deduce_N Γ q
  |DN11: forall p q, deduce_N Γ (p ↔ q) -> deduce_N Γ q -> deduce_N Γ p
  |DN12 : forall p q, deduce_N Γ (p ↔ q) -> deduce_N Γ (p → q)
  |DN13 : forall p q, deduce_N Γ (p ↔ q) -> deduce_N Γ (q → p)
  |DN14 : forall p q, deduce_N (Γ∪[¬p]) q -> deduce_N (Γ∪[¬p]) (¬q) ->
        deduce_N Γ p.
Notation "Γ ├N p" := (deduce_N Γ p)(at level 80).
Notation "├N p" := (deduce_N Φ p)(at level 80).


Ltac dng p:=
  match goal with
  | |- ?Γ ├N ?q =>
    let H0 := fresh in
      assert (H0: Γ ├N p)
  end.

Theorem N_L1 : forall Γ p q, Γ ├N (p → (q → p)).
Proof.
  intros. apply DN1. apply DN1. apply DN0; ES.
Qed.

Theorem N_L2 : forall Γ p q r, Γ ├N ((p → (q → r)) → ((p → q) → (p → r))).
Proof.
  intros. apply DN1. apply DN1. apply DN1. dng (p → q → r). { apply DN0; ES. }
  dng (p → q). { apply DN0; ES. } dng (p). { apply DN0; ES. }
  apply DN2 with q. eapply DN2; eauto. eapply DN2; eauto.
Qed.

Theorem N_L3 : forall Γ p q, Γ ├N ((¬p → ¬q)→ (q → p)).
Proof.
  intros. apply DN1. apply DN1.
  assert (Γ ∪ [p ∨ ¬ q] ∪ [q] = Γ ∪ [q] ∪ [p ∨ ¬ q]).
  { apply Extensionality_Ensembles. red. split; red; intros; ES. }
  rewrite H. pose proof DN5 (Γ ∪ [q] ∪ [p ∨ ¬ q]) p ¬ q p. apply H0.
  - apply DN0; ES.
  - apply DN1; apply DN0; ES.
  - apply DN3; apply DN0; ES.
Qed.

Theorem L_to_N : forall Γ p,Γ ├ p -> Γ ├N p.
Proof.
  intros. induction H.
  - constructor. auto.
  - apply N_L1.
  - apply N_L2.
  - apply N_L3.
  - eapply DN2; eauto.
Qed.

Lemma pos_neg_all : forall Γ p q, Γ ├ p → q -> Γ ├ ¬p → q -> Γ ├ q.
Proof.
  intros. pose proof law_inverse_prop Γ q p.
  pose proof law_inverse_prop Γ q ¬p. pose proof MP _ _ _ H1 H.
  pose proof MP _ _ _ H2 H0.
  assert (Γ ├¬q→p). { apply Deductive_Theorem. apply Deductive_Theorem in H4.
  autoL. } apply Deductive_Theorem in H3, H5.
  apply rule_Indirect with p; auto.
Qed.

Lemma des_or : forall Γ p q r, Γ ├ ¬p → q -> Γ ├ p → r -> Γ ├ q → r -> Γ ├ r.
Proof.
  intros. apply pos_neg_all with p; auto.
  assert (Γ ├ (¬p → q) → (¬p → r)). { autoL. }
  autoL.
Qed.

Lemma pq_and : forall Γ p q , Γ ├ p -> Γ ├ q -> Γ ├ p∧q.
Proof.
  intros.
  assert (Γ ├ ¬q → ¬p) by autoL.
  assert (Γ ├ p → (¬q → ¬p)). { autoL. }
  assert (Γ ├ (p → ¬q→ ¬p)→(p → ¬q) →(p → ¬p)). { autoL. }
  assert (Γ ├ ¬(p → ¬p)). 
  { apply rule_Reduction_absurdity with p.
    - autoL.
    - apply MP with p; autoL. }
  pose proof MP _ _ _ H3 H2.
   assert (Γ ├ ¬(p → ¬p)). { autoL. }
   assert (Γ ├ ¬(p → ¬p) → ¬(p → ¬q)). { autoL. } autoL.
Qed.


Theorem N_to_L : forall Γ p,Γ ├N p -> Γ ├ p.
Proof.
  intros. induction H.
  - autoL.
  - apply Deductive_Theorem. auto.
  - autoL.
  - autoL.
  - autoL.
  - eapply des_or; eauto.
  - apply pq_and; auto.
  - autoL.
  - autoL.
  - apply pq_and; auto.
  - autoL.
  - autoL.
  - autoL.
  - autoL.
  - apply rule_Indirect with q; auto.
Qed.

Theorem L_eq_N : forall Γ p,Γ ├ p <-> Γ ├N p.
Proof.
  split. apply L_to_N. apply N_to_L.
Qed.















 