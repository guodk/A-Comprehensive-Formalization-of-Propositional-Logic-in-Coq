Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import syntax.

Definition AL1 (P : Formula -> Prop) :=
  forall p q, P (p → (q → p)).
Definition AL2 (P : Formula -> Prop) :=
  forall p q r, P ((p → (q → r)) → ((p → q) → (p → r))).
Definition AL3 (P : Formula -> Prop) :=
  forall p q, P ((¬p → ¬q)→ (q → p)).
Definition AL'3 (P : Formula -> Prop) :=
  forall p q, P (¬q → (q → p)).
Definition AL'4 (P : Formula -> Prop) :=
  forall p, P (¬p → p)→ p.
Definition AF'3 (P : Formula -> Prop) :=
  forall p, P (¬¬p → p).
Definition AF3 (P : Formula -> Prop):=
  forall p q, P (¬p → ¬q) → ((¬p → q) → p).
Definition AF'4 (P : Formula -> Prop):=
  forall p q, P (p → q) → (p → ¬q) → ¬p.
Definition MP_rule (P : Formula -> Prop) :=
  forall p q, P (p → q) -> P p -> P q.

Global Hint Unfold AL1 AL2 AL3 AL'3 AL'4 MP_rule : LP.

(*classical propositional logic systems：L L' F F'*)

Section classical_logic.
Variable Γ : Ensemble Formula.
Inductive deduce_L' : Formula -> Prop :=
  | L'0 : forall p, p ∈ Γ -> deduce_L' p 
  | L'1 : AL1 _
  | L'2 : AL2 _
  | L'3 : AL'3 _
  | L'4 : AL'4 _
  | L'MP : MP_rule deduce_L'.

Inductive deduce_F : Formula -> Prop :=
  | F0 : forall p, p ∈ Γ -> deduce_F p 
  | F1 : AL1 _
  | F2 : AL2 _
  | F3 : AF3 _
  | FMP : MP_rule deduce_F.

Inductive deduce_F' : Formula -> Prop :=
  | F'0 : forall p, p ∈ Γ -> deduce_F' p 
  | F'1 : AL1 _
  | F'2 : AL2 _
  | F'3 : AF'3 _
  | F'4 : AF'4 _
  | F'MP : MP_rule deduce_F'.

End classical_logic.

Notation " Γ ├L' p " := (deduce_L' Γ p)(at level 80).
Notation " Γ ├F p " := (deduce_F Γ p)(at level 80).
Notation " Γ ├F' p " := (deduce_F' Γ p)(at level 80).

Global Hint Resolve L'0 L'3 L'4 : L'D.
Global Hint Extern 1 (_ ├L' _) => apply L'1 : L'D.
Global Hint Extern 1 (_ ├L' _) => apply L'2 : L'D.
Global Hint Extern 1 (_ ├L' _) => apply L'3 : L'D.
Global Hint Extern 1 (_ ├L' _) => apply L'4 : L'D.
Global Hint Extern 3 (_ ├L' _) => eapply L'MP : L'D.

Global Hint Extern 2 (_ ├F _) => apply F0 : FD.
Global Hint Extern 1 (_ ├F _) => apply F1 : FD.
Global Hint Extern 1 (_ ├F _) => apply F2 : FD.
Global Hint Extern 3 (_ ├F _) => eapply FMP : FD.
Global Hint Extern 1 (_ ├F _) => apply F3 : FD.

Global Hint Extern 2 (_ ├F' _) => apply F'0 : F'D.
Global Hint Extern 1 (_ ├F' _) => apply F'1 : F'D.
Global Hint Extern 1 (_ ├F' _) => apply F'2 : F'D.
Global Hint Extern 1 (_ ├F' _) => apply F'3 : F'D.
Global Hint Extern 3 (_ ├F' _) => eapply F'MP : F'D.
Global Hint Extern 1 (_ ├F' _) => apply F'4 : F'D.

 (*F'*)
Theorem UnionF' : forall Γ p q, Γ ├F' q -> Γ∪[p] ├F' q.
Proof. intros. induction H; eauto with F'D sets. Qed.

Theorem Deductive_Theorem_F' : forall Γ p q, Γ∪[p] ├F' q <-> Γ ├F' p → q.
Proof.
  split; intros.
  - induction H; eauto with *. ES; eauto with *.
  - apply F'MP with p; eauto with *. apply UnionF'; auto. Unshelve. auto.
Qed.

Theorem F'Reduction_absurdity : forall Γ p q, (Γ∪[p]) ├F' q ->
   (Γ∪[p]) ├F' ¬q -> Γ ├F' ¬p.
Proof.
  intros. pose proof (F'4 Γ p q). apply Deductive_Theorem_F' in H.
  apply Deductive_Theorem_F' in H0. pose proof F'MP. unfold MP_rule in H2.
  pose proof (F'MP _ _ _ H1 H). eauto with *.
Qed.

Theorem F'_rule_Indirect : forall Γ p q, (Γ∪[¬p]) ├F' q -> (Γ∪[¬p]) ├F' ¬q ->
  Γ ├F' p.
Proof.
  intros. assert (Γ ├F' ¬¬p). { apply (F'Reduction_absurdity _ _ _ H H0). }
  eauto with *.
Qed.

Theorem F'_Indirect : forall Γ p q, Γ ├F' (¬p → ¬q) → ((¬p → q) → p).
Proof.
  intros. repeat (apply -> Deductive_Theorem_F').
  assert (Γ ∪ [¬ p → ¬ q] ∪ [¬ p → q] ├F' ¬ p → ¬ q) by eauto with *.
  assert (Γ ∪ [¬ p → ¬ q] ∪ [¬ p → q] ├F' ¬ p → q) by eauto with *.
  apply Deductive_Theorem_F' in H. apply Deductive_Theorem_F' in H0.
  eapply F'_rule_Indirect; eauto.
Qed.

Global Hint Resolve F'_Indirect : F'D.

(*P*)
Theorem UnionF : forall Γ p q, Γ ├F q -> Γ∪[p] ├F q.
Proof. intros. induction H; eauto with *. Qed.

Theorem Deductive_Theorem_F : forall Γ p q, Γ∪[p] ├F q <-> Γ ├F p → q.
Proof.
  split; intros.
  - induction H; eauto with *. ES; eauto with *.
  - apply FMP with p; eauto with *. apply UnionF; auto.
    Unshelve. auto.
Qed.

Theorem F_rule_Indirect : forall Γ p q, Γ∪[¬p] ├F q ->  Γ∪[¬p] ├F ¬q -> Γ ├F p.
Proof.
  intros. pose proof @F3 Γ p q. apply Deductive_Theorem_F in H, H0.
  pose proof (FMP _ _ _ H1 H0). pose proof (FMP _ _ _ H2 H); auto.
Qed.

Theorem F_law_double_negation : forall p Γ, Γ ├F ¬¬p → p.
Proof.
  intros. apply Deductive_Theorem_F.
  apply F_rule_Indirect with ¬p; eauto with *.
Qed.

Global Hint Resolve F_law_double_negation  : FD.

Theorem F_absurdity : forall Γ p q, Γ ├F (p → q) → (p → ¬q) → ¬p.
Proof.
  intros. repeat (apply -> Deductive_Theorem_F).
  pose proof (F3 Γ ¬p q).
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├F(¬ ¬ p → ¬ q) → (¬ ¬ p → q) → ¬ p).
  { eauto with *. }
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├F(p → ¬ q)) by eauto with *.
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├F(¬ ¬ p → ¬ q)).
  { eauto with *. } pose proof (FMP _ _ _ H0 H2).
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├F(p → q)) by eauto with *.
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├F(¬ ¬ p → q)) by eauto with *.
  eauto with *.
Qed.
Global Hint Resolve F_absurdity : FD.

(* L' *)
Theorem UnionL' : forall p q Γ, Γ ├L' q -> Γ∪[p] ├L' q.
Proof. intros. induction H; eauto with *. Qed.

Theorem Deductive_L' : forall p q Γ, Γ∪[p] ├L' q <-> Γ ├L'p → q.
Proof.
  split; intros.
  - induction H; eauto with *. ES; eauto with *.
  - apply L'MP with p; eauto with *. apply UnionL'; auto.
    Unshelve. auto.
Qed.

Theorem L'indirect: forall p q Γ, Γ∪[¬p] ├L' q ->  Γ∪[¬p] ├L' ¬q
  -> Γ ├L' p.
Proof.
  intros. assert (Γ∪[¬p] ├L' q→p); eauto with *.
  assert (Γ∪[¬p] ├L' p); eauto with *. apply Deductive_L' in H2.
  eauto with *.
Qed.

Theorem L'_indirect: forall p q Γ, Γ ├L' (¬ p → ¬ q) → (¬ p → q) → p.
Proof.
  intros. apply Deductive_L'. apply -> Deductive_L'.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬ p → ¬ q) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬ p → q) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬ p) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬q) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' q) by eauto with *.
  eapply L'indirect; eauto.
Qed.

Global Hint Resolve L'_indirect : L'D.

Theorem eq_FF' : forall p Γ, Γ ├F p <-> Γ ├F' p.
Proof.
  split; intros; induction H; eauto with *.
Qed.

Theorem L'_to_L : forall p Γ, Γ ├L' p -> Γ ├ p.
Proof.
  intros. induction H; eauto with *.
Qed.

Theorem L_to_F : forall p Γ, Γ ├ p -> Γ ├F p.
Proof.
  intros. induction H; eauto with *.
  repeat (apply -> Deductive_Theorem_F).
  apply F_rule_Indirect with q; eauto with *.
  apply FMP with ¬ p; eauto with *.
Qed.

Theorem F_to_L' : forall p Γ, Γ ├F p -> Γ ├L' p.
Proof.
  intros. induction H; eauto with *.
Qed.