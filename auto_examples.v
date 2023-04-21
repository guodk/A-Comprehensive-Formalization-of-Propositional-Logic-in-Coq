Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.
Require Import system_equivalence.
Require Import natural_deduction.

Ltac auto_Plogic := intros;
  match goal with
  | |- _ ├N _ => apply L_eq_N; auto_Plogic
  | |- _ ├L' _ => apply F_to_L'; auto_Plogic
  | |- _ ├F _ => apply L_to_F; auto_Plogic
  | |- _ ├F' _ => apply eq_FF'; auto_Plogic
  | |- forall x, ?Q => intros; auto_Plogic
  | |- _ ├ _ => apply complete; auto_Plogic
  | |- _ => autosemantic
  end.
Example autoexample1 : forall Γ p q , Γ ├ ((p → q) → p) → p.
Proof. auto_Plogic. Qed.
Example autoexample1' : forall Γ p q , Γ ├L' ((p → q) → p) → p.
Proof. auto_Plogic. Qed.
Example autoexample2 : forall Γ p, Γ ├F (¬p → p) → p.
Proof. auto_Plogic. Qed.
Example autoexample2' : forall Γ p, Γ ╞ (¬p → p) → p.
Proof. auto_Plogic. Qed.
Example autoexample3 : forall p, [¬¬p] ├ p.
Proof. auto_Plogic. Qed.
Example autoexample3' : forall p, [¬¬p] ├F' p.
Proof. auto_Plogic. Qed.
Example autoexample4 : forall p q r, [p → q]∪[¬(q → r) → ¬p] ├ p → r.
Proof. auto_Plogic. Qed.
Example autoexample4' : forall p q r, [p → q]∪[¬(q → r) → ¬p] ├L' p → r.
Proof. auto_Plogic. Qed.
Example autoexample5 : forall p q r, [p → (q → r)] ├F q → (p → r).
Proof. auto_Plogic. Qed.
Example autoexample5' : forall p q r, [p → (q → r)] ╞ q → (p → r).
Proof. auto_Plogic. Qed.
Example autoexample6 : forall Γ p q r, Γ∪[p → q]∪[q → r] ├N p → r.
Proof. auto_Plogic. Qed.
Example autoexample6' : forall Γ p q r, Γ∪[p → q]∪[q → r] ╞ p → r.
Proof. auto_Plogic. Qed.
Example autoexample7 : forall Γ p q , Γ ├N (q → p) → (¬p → ¬q).
Proof. auto_Plogic. Qed.
Example autoexample7' : forall Γ p q, Γ ╞ (q → p) → (¬p → ¬q).
Proof. auto_Plogic. Qed.
Example autoexample8 : forall p q, Φ ├F' p → (¬q → ¬(p → q)).
Proof. auto_Plogic. Qed.
Example autoexample8' : forall p q, ├N p → (¬q → ¬(p → q)).
Proof. auto_Plogic. Qed.