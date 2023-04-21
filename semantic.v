Require Import Coq.Sets.Ensembles.
Require Import base_pc.


Notation " p ∨ q " := (¬p → q)(at level 7, right associativity).

Notation " p ∧ q " := (¬(p → ¬q))(at level 6, right associativity).

Notation " p ↔ q " := ((p → q)∧(q → p))(at level 9, right associativity).

Notation " ¬' p " := (negb p)(at level 5).
Notation "p ∨' q" := (orb p q)(at level 7).
Notation " p ∧' q " := (andb p q)(at level 6).

(*andb = fun b1 b2 : bool => if b1 then b2 else false *)
(*negb = fun b : bool => if b then false else true *)
(*orb = fun b1 b2 : bool => if b1 then true else b2 *)

Definition Contain_bool p q : bool :=
  match p, q with 
  | true, true => true
  | true, false => false
  | false, true => true
  | false, false => true
  end.

Definition Equal_bool p q : bool :=
  match p, q with 
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Notation "p →' q" := (Contain_bool p q)
  (at level 8,right associativity).

Notation " p ↔' q " := (Equal_bool p q)
  (at level 9, right associativity).

(* value *)
Definition keep_not v := (forall p, (v (¬p)) = ¬'(v p)).
Definition keep_contain v := (forall p q, (v (p → q)) = (v p) →' (v q)).
Definition value (v : Formula -> bool) :=
  keep_not v /\ keep_contain v.

Definition Tautology p := forall v, value v -> v p = true.

Notation " ╞ p " := (Tautology p)(at level 80).

(* semantic inference *)
Definition Semantic_inference (Γ:Ensemble Formula) p := forall v, value v ->
  (forall q, q ∈ Γ -> v q = true) -> v p = true.

Notation " Γ ╞ p " := (Semantic_inference Γ p)(at level 80).

Ltac debo :=
  match goal with
  | H : false = true |- _ => inversion H
  | H : true = false |- _ => inversion H
  | H : false = ?Q,
    H0 : true = ?Q |- _ => rewrite <- H in H0
  | H : ?Q = false,
    H0 : ?Q = true |- _ => rewrite H in H0
  | H :  ?Q = false,
    H0 : true = ?Q |- _ => rewrite H in H0
  | H : ?Q = true,
    H0 : false = ?Q |- _ => rewrite H in H0
  | b : bool |- _ => destruct b
  | |- forall x, ?Q => intros
  | H : keep_not _
    |- _ => rewrite -> H in *
  | H : keep_contain _
    |- _ => rewrite -> H in *
  | |- _ => auto
  end.

Ltac autobool p :=
  match p with
  | ?x →' ?y => autobool x; autobool y
  | ?x ∨' ?y => autobool x; autobool y
  | ?x ∧' ?y => autobool x; autobool y
  | ?x ↔' ?y => autobool x; autobool y
  | ¬' ?x => autobool x
  | _ => destruct p
  end.

Ltac autos := repeat debo;
  match goal with
  | |- forall x, ?Q => intros; autos
  | |- _ <-> _ => split; intros; autos
  | |- _ => red; autos
  | H : value _
    |- _ => destruct H; autos
  | |- ?l = ?r => autobool l
  | |- ?l = ?r => autobool r
  end; auto.

Lemma operation_preserved1 : forall v p q, value v -> v (p ∨ q) = (v p)∨'(v q).
Proof. autos. Qed.

Lemma operation_preserved2 : forall v p q, value v -> v (p ∧ q) = (v p)∧'(v q).
Proof. autos. Qed.

Lemma operation_preserved3 : forall v p q, value v -> v (p ↔ q) = (v p)↔'(v q).
Proof. autos. Qed.

Goal forall p q: Formula, ╞ (p → (q → p)).
Proof. autos. Qed.
Goal forall p q r: Formula,
  ╞ ((p → (q → r)) → ((p → q) → (p → r))).
Proof. autos. Qed.
Goal forall p q: Formula, ╞ ((¬p → ¬q)→ (q → p)).
Proof. autos. Qed.
Goal forall p, ╞ p → p.
Proof. autos. Qed.
Goal forall p, ╞ p ∨ ¬p.
Proof. autos. Qed.
Goal forall p, ╞ ¬ (¬ p ∧ p).
Proof. autos. Qed.
Goal forall p q, ╞ ((p → q) → p) → p.
Proof. autos. Qed.
Goal forall p q, ╞ (q → p) → (¬p → ¬q).
Proof. autos. Qed.
(* Goal forall p q r: Formula, ╞ (p ∨ q) ∨ r ↔ p ∨ (q ∨ r).
Proof. autos. Qed.
Goal forall p q: Formula, ╞ p ∨ q ↔ q ∨ p. 
Proof. autos. Qed.
Goal forall p q r: Formula, ╞ ((p ∧ q) ∧ r) ↔ (p ∧ (q ∧ r)). 
Proof. autos. Qed.
Goal forall p q r: Formula, ╞ (p ∧ (q ∨ r))↔ ((p ∧ q) ∨ (p ∧ r)). 
Proof. autos. Qed.
Goal forall p q r: Formula, ╞ (p ∨ (q ∧ r))↔ ((p ∨ q) ∧ (p ∨ r)). 
Proof. autos. Qed.
Goal forall p q: Formula, ╞ (¬ (p ∨ q)) ↔ (¬ p ∧ ¬ q).
Proof. autos. Qed.
Goal forall p q: Formula, ╞ (¬ (p ∧ q)) ↔ (¬ p ∨ ¬ q).
Proof. autos. Qed. *)

(* autot策略 证明语义推论和重言式的一些规律 *)
Ltac pose_apply_clear H0 H := pose proof H0; apply H in H0; clear H.

Ltac autot :=
  match goal with
  | |- [?p]╞ ?q =>
           red; let v := fresh "v" in
                let Hv0 := fresh "Hv0" in
           (intros v ? Hv0); assert (v p = true) by (apply Hv0; ES); autot
  | H : ?Q -> ?P,
    H0 : ?Q
    |- ?P => apply H; autot
  | |- forall x, ?Q => intros; autot
  | |- _ <-> _ => split; intros; autot
  | H: ?B \/ ?C |- _ => destruct H; autot
  | H: ?B /\ ?C |- _ => destruct H; autot
  | H : ╞ ?p ,
    H0 : value _
    |- _ => pose_apply_clear H0 H; autot
  | H : _ ╞ ?p ,
    H0 : value _
    |- _ => pose_apply_clear H0 H; autot
  | H : ?Q -> ?P,
    H0 : ?Q
    |- _ => pose_apply_clear H0 H; autot
  | |- ╞ _ => red; intros; autot
  | |- _ ╞ _ => red; intros; autot
  | H: _ -> ?P |- ?P => apply H; autot
  | |- _ => ES; autos
  end.

Ltac rewritebool :=
  match goal with
  | H: _ -> ?P |- ?P => apply H; rewritebool
  | H : _ = true |- _ => rewrite H in *; clear H; rewritebool
  | H : _ = false |- _=> rewrite H in *; clear H; rewritebool
  | H : true = _ |- _=> rewrite <- H in *; clear H; rewritebool
  | H : false = _ |- _=> rewrite <- H in *; clear H; rewritebool
  | |- _ => autos
  end.

Fact Tautology_and : forall p q ,  ╞ p ->  ╞ q ->  ╞ p ∧ q.
Proof. autot. Qed.

Fact Tautology_or : forall p q ,  ╞ p ->  ╞ q ->  ╞ p ∨ q.
Proof. autot. Qed.

Fact Tautology_latertrue : forall p q , ╞ q ->  ╞ p → q .
Proof. autot. Qed.

Fact Tautology_frontfalse : forall p q , ╞ p ->  ╞ ¬p → q.
Proof. autot. Qed.

Corollary Semantic_inference_I : forall p, Φ ╞ p <-> ╞ p.
Proof. autot. Qed.

Corollary Semantic_inference_II : forall Γ p, p ∈ Γ -> Γ ╞ p.
Proof. autot. Qed.

Corollary Semantic_inference_III : forall p, ╞ p -> forall Γ, Γ ╞ p.
Proof. autot. Qed. 

Corollary Semantic_inference_IV : forall p q, Φ∪[p] ╞ q <-> [p] ╞ q.
Proof. autot. Qed.

Lemma semantic_MP : forall Γ p q, Γ ╞ p -> Γ ╞ p → q -> Γ ╞ q.
Proof. autot. rewritebool. Qed. 
 
Lemma semantic_deny_front : forall p q, [¬p]╞ p → q.
Proof. autot. Qed.

Lemma semantic_later : forall p q, [q]╞ p → q.
Proof. autot. Qed.

(* semantic deductive theorem *)
Lemma semantic_deductive : forall Γ p q, Γ∪[p] ╞ q <-> Γ ╞ p → q.
Proof.
  split; intros; red; intros; remember (v p) as b.
  - pose proof H _ H0. destruct H0. rewrite H3. destruct b.
    + assert (v q = true) by (apply H2; ES). autos.
    + autos.
  - pose proof H _ H0. destruct H0. rewrite H3 in *. destruct b.
    + assert ((v p) →' (v q) = true) by (apply H2; ES). rewrite <-Heqb in *.
      autos.
    + assert (v p = true) by (apply H1; ES). autos.
Qed.

(* autosemantic，prove all like
   Γ ╞ p
   [p0] ╞ p
   Γ ∪ [p0] ╞ p
   [p0] ∪ ... ∪ [pn] ╞ p
   Γ ∪ [p0] ∪ ... ∪ [pn] ╞ p  *)
Ltac autosemantic :=
  match goal with
  | |- ╞ _ => autos
  | |- Φ ╞ _ => apply Semantic_inference_I; autosemantic
  | |- [_]╞ _ => apply Semantic_inference_IV; autosemantic
  | |- _∪[_]╞ _ => apply <-semantic_deductive; autosemantic
  | |- forall x, ?Q => intros; autosemantic
  | |- _ => apply Semantic_inference_III; autosemantic
  end.

Goal forall Γ p, Γ ╞ (¬p → p) → p.
Proof. autosemantic. Qed.
Goal forall Γ p q, Γ ╞ (q → p) → (¬p → ¬q).
Proof. autosemantic. Qed.
Goal forall p q r, [p → q]∪[q → r] ╞ p → r.
Proof. autosemantic. Qed.
Goal forall Γ p q r, Γ ╞ (p ∨ q) ∨ r ↔ p ∨ (q ∨ r).
Proof. autosemantic. Qed.
