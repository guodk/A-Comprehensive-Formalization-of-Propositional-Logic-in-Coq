Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.Classical.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Div2.

Definition function_injective {A B} (f: A -> B): Prop :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition function_surjective {A B} (f: A -> B): Prop :=
  forall b, exists a, f a = b.

Inductive function_bijective {A B} (f: A -> B): Prop :=
  | fun_bij_intro : function_injective f -> function_surjective f -> function_bijective f.

Record injection (A B: Type): Type := {
  inj_f:> A -> B;
  in_inj: function_injective inj_f
}.

Record surjection (A B: Type): Type := {
  sur_f:> A -> B;
  su_surj: function_surjective sur_f
}.

Record bijection (A B: Type): Type := {
  bij_f:> A -> B;
  in_bij: function_injective bij_f;
  su_bij: function_surjective bij_f
}.

Definition injection_trans {A B C} (f1: injection A B) (f2: injection B C): injection A C.
  apply (Build_injection _ _ (fun a => f2 (f1 a))).
  hnf; intros. apply (in_inj _ _ f2) in H. apply (in_inj _ _ f1) in H. auto.
Defined.

Definition bijection_sym {A B} (f: bijection A B): bijection B A.
  apply (Build_bijection _ _ (fun b => proj1_sig (constructive_indefinite_description _ ((su_bij _ _ f) b)))).
  - hnf; intros. repeat destruct constructive_indefinite_description. simpl in H.
    congruence.
  - hnf; intros. exists (bij_f _ _ f b). destruct constructive_indefinite_description.
    simpl. apply (in_bij _ _ f). auto.
Defined.

Definition sum_injection {A1 B1 A2 B2} (f1: injection A1 B1) (f2: injection A2 B2): injection (sum A1 A2) (sum B1 B2).
  apply (Build_injection _ _ (fun a => match a with inl x => inl (f1 x) | inr y => inr (f2 y) end)).
  hnf; intros. destruct a1, a2; try inversion H.
  - inversion H. apply (in_inj _ _ f1) in H1. f_equal; auto.
  - inversion H. apply (in_inj _ _ _) in H1. f_equal; auto.
Defined.

Definition prod_injection {A1 B1 A2 B2} (f1: injection A1 B1) (f2: injection A2 B2): injection (prod A1 A2) (prod B1 B2).
  apply (Build_injection _ _ (fun m =>
          match m with
          | (m1, m2) => (f1 m1, f2 m2) end )).
  hnf; intros. destruct a1, a2.
  inversion H. apply in_inj in H1, H2. congruence.
Defined.

Definition sigT_injection (I: Type) (A: I -> Type) (B: Type) (f: forall i: I, injection (A i) B): injection (sigT A) (I * B).
  apply (Build_injection _ _ (fun a => (projT1 a, f (projT1 a) (projT2 a)))).
  hnf; intros. inversion H. destruct a1,a2. simpl in *.
  subst. apply (in_inj _ _ (f x0)) in H2. congruence.
Defined.

Definition bijection_injection {A B} (f: bijection A B): injection A B :=
  Build_injection _ _ f (in_bij _ _ f).

Definition nat2_nat_bijection: bijection (sum nat nat) nat.
  apply (Build_bijection _ _ (fun n => match n with | inl n => n + n | inr n => S (n + n) end)).
  - hnf; intros. destruct a1 eqn:Ha1, a2 eqn:Ha2; try lia; f_equal; lia.
  - hnf; intros. assert (forall n, exists m, n= m + m \/ n = S (m + m)).
    { intros. induction n. eauto. destruct IHn. destruct H.
      - exists x; lia.
      - exists (S x); lia. }
    destruct (H b) as [n []].
    + exists (inl n). auto.
    + exists (inr n); auto.
Defined.

Definition natnat_nat_bijection: bijection (prod nat nat) nat.
  set (fix sum (x : nat) : nat := match x with
       | 0 => 0
       | S x0 => S x0 + sum x0
       end) as f.
  apply (Build_bijection _ _
    (fun n => match n with | (n1, n2) => f (n1+n2) + n1 end)).
  - hnf; intros. destruct a1 as (a11, a12), a2 as (a21, a22).
    assert (forall m1 m2, m1 < m2 -> f m1 + m1 < f m2).
    { intros. remember (m2 - m1 - 1) as d; assert (m2 = (S d) + m1) by lia.
      subst m2. clear. induction d; simpl in *; lia. }
    destruct (Compare_dec.le_lt_dec (a11 + a12) (a21 + a22)).
    + destruct (Lt.le_lt_or_eq _ _ l).
      * pose proof H0 _ _ H1. lia.
      * rewrite H1 in *. assert (a11=a21) by lia. subst.
        assert (a12 = a22) by lia. auto.
    + apply H0 in l. lia.
  - hnf; intros. assert ( forall a, exists s, f s <= a < f (S s)).
    { induction a. exists 0. auto. destruct IHa as [s Hs].
      remember (a - f s) as d.
      destruct (PeanoNat.Nat.lt_ge_cases d s).
      + exists s. simpl in *. lia.
      + exists (S s). simpl in *; lia. }
    destruct (H b) as [s Hs].
    remember (b - (f s)) as a1. assert (a1 <= s) by (unfold f in *; lia).
    exists (a1, s-a1). replace (a1 + (s - a1)) with s by lia. 
    lia.
Defined.

Definition Countable (A: Type): Type := injection A nat.

Definition injection_Countable {A B} (R: injection A B) (CB: Countable B): Countable A := injection_trans R CB.

Definition bijection_Countable {A B} (R: bijection A B) (CB: Countable B): Countable A := injection_Countable (bijection_injection R) CB.

Definition sum_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (sum A B) :=
  injection_trans (sum_injection CA CB) (bijection_injection nat2_nat_bijection).

Definition prod_Countable {A B} (CA: Countable A) (CB: Countable B): Countable (prod A B) :=
  injection_trans (prod_injection CA CB) (bijection_injection natnat_nat_bijection).

Definition nCountable_Countable {A: nat -> Type} (CA: forall n, Countable (A n)): Countable (sigT A) :=
  injection_trans (sigT_injection _ _ _ CA) (bijection_injection natnat_nat_bijection).

Definition nat_Countable : Countable nat.
  apply (Build_injection _ _ (fun n => n )).
  hnf; intros. eauto.
Defined.

Ltac solve_Countable :=
  match goal with
  | |- Countable (sum _ _) => apply sum_Countable; solve_Countable
  | |- Countable (prod _ _) => apply prod_Countable; solve_Countable
  | |- Countable (sigT _) => try (apply nCountable_Countable; intro; solve_Countable)
  | |- Countable nat => apply nat_Countable
  | _ => try assumption
  end.








