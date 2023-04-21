Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import auto_examples.

Theorem compactness : forall Γ p, Γ ╞ p <-> exists Γ' , Γ'⊆Γ /\ Finite _ Γ' /\
  Γ'╞ p.
Proof.
  split; intros.
  - apply complete in H.
    induction H.
    + exists [p]. split.
      * red; intros. destruct H0. auto.
      * split; try auto_Plogic.
         pose proof Empty_is_finite Formula.
         assert ([p]=(Add _ Φ p)). { apply Extensionality_Ensembles.
         split.
         - red; intros; ES.
         - red; intros. destruct H1. ES. auto. }
         rewrite H1; constructor; auto. intro. ES.
    + exists Φ. repeat split.
      * red; ES.
      * constructor.
      * auto_Plogic.
    + exists Φ. repeat split.
      * red; ES.
      * constructor.
      * auto_Plogic.
    + exists Φ. repeat split.
      * red; ES.
      * constructor.
      * auto_Plogic.
    + destruct IHdeduce_L1 as [Γ1 [? []]], IHdeduce_L2 as [Γ2 [? []]].
      exists (Γ1∪Γ2). repeat split.
      * red; intros. ES.
      * apply Union_preserves_Finite; auto.
      * apply soundness_L. apply complete in H3, H6.
        pose proof Union_l _ _ H3 Γ2.  pose proof Union_r _ _ H6 Γ1.
        autoL.
  - destruct H as [? [? []]]. apply soundness_L. apply complete in H1.
    eapply subsetprove; eauto.
Qed.

Theorem compactness_consistence : forall Γ, consistence Γ <->
  (forall Γ' , Γ'⊆Γ -> Finite _ Γ' -> consistence Γ').
Proof.
  split.
  - intros. eapply subsetNocontra; eauto.
  - intros. red. intros. intro. destruct H0.
    apply soundness_L in H0, H1.
    apply compactness in H0, H1.
    destruct H0 as [A [? []]], H1 as [B [? []]].
    pose proof Union_preserves_Finite _ A B H2 H4.
    assert ((A ∪ B)⊆ Γ) by ES.
    pose proof H _ H7 H6 q. destruct H8. apply complete in H3, H5. split.
    + apply subsetprove with A; ES.
    + apply subsetprove with B; ES.
Qed.



         