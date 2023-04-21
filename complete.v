Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import Mappings.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.Classical.
Require Import Classical_Pred_Type.
Require Import Coq.micromega.Lia.
Require Import bijection_nat_Formula.

Definition Contradiciton Γ := exists q, Γ ├ q /\ Γ ├ ¬q.
Definition consistence Γ:= forall q, ~ (Γ ├ q /\ Γ ├ ¬q).

(*soundness*)
Theorem soundness_L : forall Γ p, Γ ├ p -> Γ ╞ p.
Proof.
  intros. red. intros. induction H; autot. rewrite IHdeduce_L2 in *.
  inversion IHdeduce_L1.
Qed.

Fixpoint vtrue p :=
  match p with 
  | Var _ => true
  | ¬ q => ¬' (vtrue q)
  | q → r => (vtrue q) →' (vtrue r)
  end.

Fixpoint vfalse p :=
  match p with 
  | Var _ => false
  | ¬ q => ¬' (vfalse q)
  | q → r => (vfalse q) →' (vfalse r)
  end.

Theorem consistence_L :  consistence Φ.
Proof.
  unfold consistence. intros.
  intro. destruct H. apply soundness_L in H,H0.
  red in H; red in H0. assert (value vtrue).
  { red; split; red; auto. }
  assert (P: forall v q, q ∈ Φ -> v q = true).
  { intros. destruct H2. }
  pose proof (H vtrue H1). pose proof (H0 vtrue H1).
  pose proof P as P1. apply H2 in P; apply H3 in P1.
  simpl in P; simpl in P1.
  rewrite P in P1. inversion P1.
Qed.

Fixpoint mapf Γ n (f: nat-> Formula) : Ensemble Formula := 
    match n with
    | O => Γ
    | S m => match (classicT (consistence ((mapf Γ m f)∪[f m]))) with
              | left _ => mapf Γ m f ∪ [f m]
              | right _ => (mapf Γ m f)
              end
     end.

Definition maxmapf Γ f: Ensemble Formula :=
  fun p => exists n, p ∈ (mapf Γ n f).

Definition Mapf Γ n f: Ensemble Formula :=
  fun p => exists m, m<=n /\  p ∈ (mapf Γ n f).

Definition valuemaxf Γ (p:Formula) : bool := 
    match (classicT (p ∈ Γ)) with
              | left _ => true
              | right _ => false
     end.

Fact MapfI : forall Γ f n, 
  (Mapf Γ n f) = (mapf Γ n f).
Proof.
  intros. induction n.
  - simpl. apply Extensionality_Ensembles; split; intros.
    + red; intros. destruct H as [? [_ ?]]. simpl in H. auto.
    + red; red. intros. red. exists 0. auto.
  - apply Extensionality_Ensembles; split; intros.
    + red; intros. red in H. red in H. destruct H as [m [_ H]]. auto.
    + red; intros. red. red. eauto.
Qed.

Fact mapfIncluded_aux : forall Γ f m n, m<=n ->
  (mapf Γ m f) ⊆ (mapf Γ n f).
Proof.
  induction n.
  - intros. red. intros. induction m; auto. inversion H.
  - intros. red. intros. assert (m<=n \/ m=S n).
    { inversion H; auto. } destruct H1. apply IHn in H1. apply H1 in H0.
    simpl. destruct classicT. apply UnionI. left; auto. auto. subst; auto.
Qed.
  
Fact mapfIncluded : forall Γ f m n,
  (mapf Γ m f) ⊆ (mapf Γ n f) \/  (mapf Γ n f) ⊆ (mapf Γ m f).
Proof.
  intros. assert ( m<=n \/ n<=m).
  { induction m. left. induction n; auto. destruct IHm.
    - inversion H. right. apply le_S; apply le_n. subst.
      left. apply le_n_S. auto.
    - right. apply le_S. auto. }
  destruct H.
  - left. apply mapfIncluded_aux; auto.
  - right. apply mapfIncluded_aux; auto.
Qed.

Fact subsetprove : forall A B p, A⊆B -> A ├ p -> B ├ p.
Proof.
  intros. red in H. induction H0; autoL.
Qed.
Fact subsetNocontra : forall A B , A⊆B -> consistence B ->
  consistence A.
Proof.
  intros. red. intros. intro. red in H0. destruct (H0 q).
  destruct H1; split; eapply subsetprove; eauto.
Qed.


Lemma maxmapfI : forall Γ f p, (maxmapf Γ f) ├ p -> exists n, (mapf Γ n f) ├ p.
Proof.
  intros. induction H.
  - red in H. red in H. destruct H. red in H. exists x. apply L0. auto.
  - exists 0; autoL.
  - exists 0; autoL.
  - exists 0; autoL.
  - destruct IHdeduce_L1, IHdeduce_L2.
    destruct (mapfIncluded Γ f x x0). pose proof subsetprove _ _ _ H3 H1.
    exists x0. apply MP with p; auto.
    pose proof subsetprove _ _ _ H3 H2. exists x. apply MP with p; auto.
Qed.

Lemma redundancy_lemma : forall Γ p, Γ∪[¬p] ├ p -> Γ ├ p.
Proof.
  intros. apply Deductive_Theorem in H. assert (Γ ├ (¬ p → p) → p); autoL.
Qed.

Definition maximal_consistent_set Γ := consistence Γ /\
  forall p, consistence (Γ∪[p]) -> p∈Γ.



Fact boom : forall Γ, ~ consistence Γ -> forall p, Γ ├ p.
Proof.
  intros. unfold consistence in H. apply not_all_not_ex in H as [? []].
  assert (Γ ├ x → ¬ x → p); autoL.
Qed.
  

Lemma No_contra : forall Γ, consistence Γ ->
  forall p, consistence (Γ ∪ [p])\/consistence (Γ ∪ [¬p]).
Proof.
  intros. destruct (classic (consistence (Γ ∪ [¬p]))); auto.
  pose proof boom. pose proof H1 (Γ ∪ [¬ p]) H0. pose proof H2 p.
  apply redundancy_lemma in H3. destruct (classic (consistence (Γ ∪ [p]))); auto.
  pose proof H1 (Γ ∪ [p]) H4. assert (forall p0, Γ ├ p0).
  { intros. pose proof H5 p0. apply Deductive_Theorem in H6.
    apply MP with p; auto. } red in H. pose proof H p.
    destruct H7; split; auto.
Qed.

Lemma valuemaxfI : forall Γ, maximal_consistent_set Γ -> value (valuemaxf Γ).
Proof.
  intros. destruct H. pose proof H as consist. red in H. split; intros. 
  - unfold valuemaxf. red. intros. destruct classicT.
    + destruct classicT. apply L0 in i, i0. pose proof H p; tauto.
      auto.
    + destruct classicT. auto. destruct (classic (consistence (Γ ∪ [p]))).
      * apply H0 in H1. tauto.
      * pose proof No_contra _ consist. pose proof H2 p.
        destruct H3; apply H0 in H3; auto.
  - unfold valuemaxf. red; intros. destruct classicT.
    + destruct classicT.
      * pose proof No_contra _ consist q. destruct classicT. auto. destruct n.
        destruct H1. apply H0 in H1. auto. apply H0 in H1. red in consist.
        pose proof consist q. destruct H2. apply L0 in i, i0, H1. split; autoL.
      * destruct (if classicT (q ∈ Γ) then true else false); auto.
    + destruct classicT.
      * destruct classicT; auto. destruct n. apply H0. red. intros.
        intro. destruct H1. apply Deductive_Theorem in H1, H2.
        apply L0 in i, i0. assert (Γ ├ (p → q)). { pose proof L1 Γ q p.
        apply MP with q; auto. } pose proof MP _ _ _ H1 H3.
        pose proof MP _ _ _ H2 H3.
        red in consist. destruct (consist q0). split; auto.
      * pose proof No_contra _ consist p. destruct H1.
        -- apply H0 in H1; tauto.
        -- apply H0 in H1. destruct n. apply H0. red. intros. intro.
           destruct H2. assert (Γ├ ¬ p → p → q) by autoL. apply L0 in H1.
           pose proof MP _ _ _ H4 H1. apply Deductive_Theorem in H2, H3.
           pose proof MP _ _ _ H2 H5. pose proof MP _ _ _ H3 H5. red in consist.
           pose proof consist q0. tauto.
Qed.

Lemma valuemaxfII : forall Γ, maximal_consistent_set Γ ->
  forall p, (valuemaxf Γ) p = true <-> p∈Γ.
Proof.
  intros. induction p.
  - split; intros.
    + unfold valuemaxf in H0. destruct classicT; auto. inversion H0.
    + unfold valuemaxf. destruct classicT; auto.
  - split; intros.
    + unfold valuemaxf in H0. destruct classicT. auto. inversion H0.
    + unfold valuemaxf; destruct classicT; auto.
  - split; intros.
    + unfold valuemaxf in H0. destruct classicT; auto. inversion H0.
    + unfold valuemaxf; destruct classicT; auto.
Qed.

(* completeness *) 
Theorem complete : forall Γ p, Γ ╞ p -> Γ ├ p.
Proof.
  intros. pose proof bijection_nat_formula as NF. destruct NF as [f ?].
  destruct (classic (Γ ├ p)); auto. set (Γ':= Γ∪[¬p]).
  assert (forall n, consistence (mapf Γ' n f)).
  { intros. induction n.
    - simpl. red. intros. intro. destruct H0, H1.
      apply (rule_Indirect _ _ _ H0 H1).
    - red. intros. intro. pose proof H1 as contradictionP.
      destruct H1. simpl in H1, H2. destruct classicT as [c|d].
      + red in c. pose proof c q. tauto.
      + red in IHn. pose proof IHn q. tauto. }
  assert (consistence (maxmapf Γ' f)).
  { red. intros. intro. destruct H2. apply maxmapfI in H2 as [], H3 as [].
    destruct (mapfIncluded Γ' f x x0). pose proof subsetprove _ _ _ H4 H2.
    pose proof H1 x0. red in H6. pose proof H6 q. tauto.
    pose proof subsetprove _ _ _ H4 H3.
    pose proof H1 x. red in H6. pose proof H6 q. tauto. }
  assert (maxsetproperty : forall p, consistence ((maxmapf Γ' f)∪[p]) 
    -> p∈(maxmapf Γ' f)).
  { intros. red in in_bij, su_bij. pose proof su_bij p0 as [a ?H].
    red. red. exists (S a). pose proof H1 (S a). simpl in H5. destruct classicT.
    - simpl. destruct classicT. subst; ES. tauto.
    - simpl. destruct classicT. tauto. subst.
      assert ((mapf Γ' a f ∪ [f a]) ⊆ (maxmapf Γ' f ∪ [f a])).
      { red; intros. ES. left. red. red. eauto. }
    pose proof subsetNocontra _ _ H4 H3. tauto. }
  assert (mc : maximal_consistent_set (maxmapf Γ' f)). { split; auto. }
  pose proof (valuemaxfI _ mc). pose proof (valuemaxfII _ mc).
  pose proof H1 0. simpl in H5. pose proof maxsetproperty ¬p.
  assert ((maxmapf Γ' f ∪ [¬ p])= maxmapf Γ' f).
  { apply Extensionality_Ensembles; split; intros. 
    red; intros. destruct H7; auto. ES. apply H6.
    apply subsetNocontra with (maxmapf Γ' f); auto. red; intros.
    destruct H8; auto. ES. red. red. exists 0. simpl. unfold Γ'; ES. ES. }
  rewrite H7 in *. pose proof H6 H2. apply H4 in H8. red in H.
  apply H in H3. apply H4 in H3, H8. destruct (H2 p); split; autoL.
  intros. apply H4. red; red. exists 0. simpl. unfold Γ'; ES.
Qed.
Print Assumptions complete.

