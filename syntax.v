Require Import Coq.Sets.Ensembles.
Require Import base_pc.

Reserved Notation " Γ ├ p " (at level 80).

Inductive deduce_L (Γ : Ensemble Formula): Formula -> Prop :=
  | L0 : forall p, p ∈ Γ -> Γ ├ p 
  | L1 : forall p q, Γ ├ (p → (q → p))
  | L2 : forall p q r, Γ ├ ((p → (q → r)) → ((p → q) → (p → r)))
  | L3 : forall p q, Γ ├ ((¬p → ¬q)→ (q → p))
  | MP : forall p q, Γ ├ (p → q) -> Γ ├ p -> Γ ├ q
where " Γ ├ p " := (deduce_L Γ p).

Global Hint Constructors deduce_L : LD.
Fact Union_l : forall Γ p, Γ ├ p -> forall A, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Fact Union_r : forall Γ p , Γ ├ p -> forall A, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Ltac autoL :=
  match goal with
  | H: ?Γ ├ ?p |- ?Γ ∪ ?A ├ ?p => apply Union_l; auto
  | H: ?Γ ├ ?p |- ?A ∪ ?Γ ├ ?p => apply Union_r; auto
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?Γ ├ ?p ,
    H1: ?Γ ├ ?p → ?q
    |- ?Γ ├ ?q => apply MP with p; auto
  | H: ?Γ ├ ?p
    |- ?Γ ├ ?q → ?p =>
      let H0 := fresh in
      assert (H0: Γ ├ p → q → p) by (apply L1); autoL
  | |- ?Γ ├ ?x => eauto with LD sets
  | |- forall a, ?Q => intros; autoL
  end.

Ltac later :=
  match goal with
  | |- ?Γ ├ ?q → ?p =>
    let H0 := fresh in
      assert (H0: Γ ├ p) by (autoL); autoL
  end.

Lemma law_identity : forall Γ p, Γ ├ p → p.
Proof. autoL. Unshelve. exact p. Qed.
Global Hint Resolve law_identity : LD.

Lemma law_deny_antecedent : forall Γ p q, Γ ├ ¬q → (q → p).
Proof. autoL. Qed.
Global Hint Resolve law_deny_antecedent : LD.

Theorem Deductive_Theorem : forall Γ p q, Γ∪[p] ├ q <-> Γ ├ p → q.
Proof.
  split; intros.
  - induction H; repeat (autoL; ES).
  - apply MP with p; autoL.
Qed.

Lemma law_negetion_affirmation : forall Γ p, Γ ├ (¬p → p) → p.
Proof.
  intros. apply -> Deductive_Theorem. 
  assert (Γ ∪ [¬ p → p] ├ (¬p → p) → (¬p → ¬(¬p → p))) by autoL.
  assert (Γ ∪ [¬ p → p] ├ ¬p → ¬(¬p → p)) by autoL.
  autoL.
Qed.
Global Hint Resolve law_negetion_affirmation : LD.

Fact law_double_negation_second : forall Γ p , Γ ├ p → ¬¬p.
Proof. autoL. Qed.
Global Hint Resolve law_double_negation_second : LD.

Ltac Single_Union :=
  match goal with 
  | |- ?Γ ∪ [?p] ├ ?q => assert(Γ ∪ [p] ├ p); autoL
  end.

Fact law_inverse_prop : forall Γ p q, Γ ├ (q → p) → (¬p → ¬q).
Proof.
  intros. apply Deductive_Theorem.
  assert (Γ ∪ [q → p] ├ ¬¬q → q) by autoL.
  assert (Γ ∪ [q → p] ├ p → ¬¬p) by autoL.
  assert (Γ ∪ [q → p] ├ q → p) by autoL.
  assert (Γ ∪ [q → p] ├ ¬¬q → p) by autoL.
  autoL.
Qed.
Global Hint Resolve law_inverse_prop : LD.

Fact law_peirce : forall Γ p q , Γ ├ ((p → q) → p) → p.
Proof.
  intros. apply Deductive_Theorem. assert (Γ ├ ¬p → (p →q)) by 
  autoL. apply Union_l with (A:=[(p → q) → p]) in H.
  Single_Union.
Qed.
Global Hint Resolve law_peirce : LD.

(* law of indirect proof *)
Theorem rule_Indirect : forall Γ p q, Γ∪[¬p] ├ q -> Γ∪[¬p] ├ ¬q -> Γ ├ p.
Proof.
  intros. assert (Γ∪[¬p] ├ p) by autoL.
  apply Deductive_Theorem in H1; autoL.
  Unshelve. auto. auto. auto.
Qed.

Corollary law_double_negation_aux : forall p, [¬¬p] ├ p.
Proof. autoL. Unshelve. auto. Qed.

Corollary law_double_negation : forall  Γ p, Γ ├ ¬¬p → p.
Proof.
  intros; apply Deductive_Theorem. autoL.
Qed.
Global Hint Resolve law_double_negation : LD.

Lemma syllogism : forall Γ p q r , Γ∪[p] ├ q -> Γ∪[r] ├ p -> Γ∪[r] ├ q.
Proof.
  intros. apply Deductive_Theorem in H. apply Deductive_Theorem in H0.
  assert (Γ ∪ [r] ├ r) by autoL. pose proof (Union_l _ _ H [r]).
  pose proof (Union_l _ _ H0 [r]). autoL.
Qed.

(* law of reduction to absurdity *)
Theorem rule_Reduction_absurdity :
  forall Γ p q, Γ∪[p] ├ q -> Γ∪[p] ├ ¬q -> Γ ├ ¬p.
Proof.
  intros. assert (Γ ∪ [¬¬p] ├ q). { eapply syllogism; autoL. } 
  assert (Γ ∪ [¬¬p] ├ ¬q). { eapply syllogism; autoL. }
  apply (rule_Indirect _ _ _ H1 H2); auto.
Qed.