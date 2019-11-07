Inductive pol := Pos | Neg.

Inductive term : Set :=
| var (v : nat)
| join (a b : term)
| meet (a b : term)
| top
| bot
| prod (a : term) (b : term)
| fn (dom : term) (rng : term).

Require Import List.
Open Scope list_scope.

Notation "Γ , [ A ] , Δ" := (Γ ++ A :: Δ) (at level 65).

Fact app_prefix {Γ Γ' Δ} {A : term} : Γ ++ (Γ' , [ A ] , Δ) = (Γ ++ Γ') , [ A ] , Δ.
apply app_assoc. Qed.

Fact app_suffix {Γ Δ Δ'} {A : term} : (Γ , [ A ] , Δ) ++ Δ' = Γ , [ A ] , (Δ ++ Δ').
symmetry. apply (app_assoc Γ (A :: Δ) Δ'). Qed.


Inductive term_field : Set := f_dom | f_range | f_left | f_right.

Fixpoint filter_field (f : term_field) (ts : list term) :=
  match ts with
  | nil => nil
  | fn d r :: ts =>
    match f with
    | f_dom => d :: filter_field f ts
    | f_range => r :: filter_field f ts
    | _ => filter_field f ts
    end
  | prod l r :: ts =>
    match f with
    | f_left => l :: filter_field f ts
    | f_right => r :: filter_field f ts
    | _ => filter_field f ts
    end
  | _ :: ts => filter_field f ts
  end. 

Lemma filter_field_app {f ts ts'} : filter_field f (ts ++ ts') = filter_field f ts ++ filter_field f ts'.
induction ts as [| t ts]; auto; destruct t; destruct f; simpl; f_equal; auto. Qed.

Inductive seq : list term -> list term -> Prop :=
| hyp {Γ₁ Γ₂ Δ₁ Δ₂ v} :
  seq (Γ₁ ++ var v :: Γ₂) (Δ₁ ++ var v :: Δ₂)
| meet_l {Γ₁ Γ₂ Δ A B} :
  seq (Γ₁ ++ A :: B :: Γ₂) Δ ->
  seq (Γ₁ ++ meet A B :: Γ₂) Δ
| meet_r {Γ Δ₁ Δ₂ A B} :
  seq Γ (Δ₁ ++ A :: Δ₂) ->
  seq Γ (Δ₁ ++ B :: Δ₂) ->
  seq Γ (Δ₁ ++ meet A B :: Δ₂)
| join_l {Γ₁ Γ₂ Δ A B} :
  seq (Γ₁ ++ A :: Γ₂) Δ ->
  seq (Γ₁ ++ B :: Γ₂) Δ ->
  seq (Γ₁ ++ join A B :: Γ₂) Δ
| join_r {Γ Δ₁ Δ₂ A B} :
  seq Γ (Δ₁ ++ A :: B :: Δ₂) ->
  seq Γ (Δ₁ ++ join A B :: Δ₂)
| bot_l {Γ₁ Γ₂ Δ} :
  seq (Γ₁ ++ bot :: Γ₂) Δ
| top_r {Γ Δ₁ Δ₂} :
  seq Γ (Δ₁ ++ top :: Δ₂)
| prod_sub {Γ Δ} :
  seq (filter_field f_left Γ) (filter_field f_left Δ) ->
  seq (filter_field f_right Γ) (filter_field f_right Δ) ->
  seq Γ Δ
| fn_sub {Γ Δ} :
  seq (filter_field f_dom Δ) (filter_field f_dom Γ) ->
  seq (filter_field f_range Γ) (filter_field f_range Δ) ->
  seq Γ Δ.


Ltac seqrule_prim :=
  first [apply hyp | apply meet_l | apply meet_r | apply join_l | apply join_r | apply bot_l | apply top_r].
Ltac seqrule_prefix := first
  [ seqrule_prim
  | rewrite app_prefix; seqrule_prefix; rewrite <- app_prefix ].
Ltac seqrule_suffix := first
  [ seqrule_prim
  | rewrite app_suffix; seqrule_suffix; (rewrite <- app_suffix || (rewrite app_comm_cons; rewrite <- app_suffix)) ].
Ltac seqrule := (seqrule_prefix || seqrule_suffix); firstorder.
Ltac seqrule_prod := apply prod_sub; repeat rewrite filter_field_app; simpl; firstorder.
Ltac seqrule_fn := apply fn_sub; repeat rewrite filter_field_app; simpl; firstorder.

Fact shift {A} {Γ Δ : list A} {x y : A} :
  Γ ++ x :: y :: Δ = (Γ ++ (x :: nil)) ++ y :: Δ.
exact (app_assoc Γ (x :: nil) _). Qed.

Fact shift' {A} {Γ Δ : list A} {x y : A} :
  x :: Γ ++ y :: Δ = (x :: Γ) ++ y :: Δ.
reflexivity. Qed.

Fact shift_nil {A} {Δ : list A} {x : A} :
  x :: Δ = nil ++ x :: Δ.
reflexivity. Qed.

Lemma refl {A} : forall {Γ₁ Γ₂ Δ₁ Δ₂}, seq (Γ₁ ++ A :: Γ₂) (Δ₁ ++ A :: Δ₂).
Proof.
  induction A; intros; try repeat (seqrule; auto); try (rewrite shift; auto); try solve [seqrule_prod | seqrule_fn].
Qed.

Lemma weak1 {Γ Δ} (Seq : seq Γ Δ) : (forall {X}, seq (X :: Γ) Δ) /\ (forall {X}, seq Γ (X :: Δ)).
Proof.
  induction Seq; intros; firstorder; try rewrite app_comm_cons;
  solve [seqrule | destruct X; seqrule_prod | destruct X; seqrule_fn ].
Qed.

Lemma weakN {Γ Δ} (Seq : seq Γ Δ) : forall Γ' Δ', seq (Γ' ++ Γ) (Δ' ++ Δ).
induction Γ'; induction Δ'; simpl in *; repeat apply weak1; auto. apply (IHΓ' nil). Qed.

Require Import Coq.Sorting.Permutation.

Fact in_unsplit {A : Set} (x : A) (xs₁ xs₂ : list A) : In x (xs₁ ++ x :: xs₂).
apply in_or_app; simpl; auto. Qed.

Lemma perm_elem {A : Set} : forall {xs₁ xs₂ : list A} {a Y}, 
    Permutation (xs₁ ++ a :: xs₂) Y ->
    exists ys₁ ys₂, Y = ys₁ ++ a :: ys₂ /\ Permutation (xs₁ ++ xs₂) (ys₁ ++ ys₂).
Proof.
  intros. destruct (In_split a Y) as [ys₁ [ys₂ ->]].
  - eapply Permutation_in; try eassumption. apply in_unsplit.
  - exists ys₁; exists ys₂. split; auto. eauto using Permutation_app_inv.
Qed.

Lemma perm_inside {A : Set} : forall {xs₁ xs₂ ys₁ ys₂ : list A} {a},
    Permutation (xs₁ ++ xs₂) (ys₁ ++ ys₂) -> Permutation (xs₁ ++ a :: xs₂) (ys₁ ++ a :: ys₂).
Proof.
  intros.
  eapply Permutation_trans. apply Permutation_sym. apply Permutation_middle.
  apply Permutation_cons_app. auto.
Qed.

Inductive Permutation' {A : Set} : list A -> list A -> Prop :=
| is_permutation_nil : Permutation' nil nil
| is_permutation_cons {x : A} {xs ys₁ ys₂} : Permutation' xs (ys₁ ++ ys₂) -> Permutation' (x :: xs) (ys₁ ++ x :: ys₂).

Lemma Permutation'_equiv {A : Set} {xs ys : list A} : Permutation xs ys <-> Permutation' xs ys.
Proof.
  split.
  - revert ys. induction xs.
    * destruct ys as [|y ys]. constructor. intro H. contradiction (Permutation_nil_cons H).
    * intros ys HPerm. destruct (@perm_elem _ nil _ _ _ HPerm) as [ys1 [ys2 [-> HPerm']]].
      constructor. auto.
  - induction 1. constructor. apply (@perm_inside _ nil). auto.
Qed.

Lemma perm_filter_field : forall f xs ys, Permutation xs ys -> Permutation (filter_field f xs) (filter_field f ys).
Proof.
  cut (forall f xs ys, Permutation' xs ys -> Permutation' (filter_field f xs) (filter_field f ys)).
  intros f xs ys H HP. apply Permutation'_equiv. apply Permutation'_equiv in HP. auto.
  induction 1; try constructor.
  rewrite filter_field_app. rewrite filter_field_app in IHPermutation'.
  destruct x; simpl; try constructor; auto;
    destruct f; simpl in *; try constructor; auto.
Qed.

Theorem permutation {Γ Δ} (Seq : seq Γ Δ) : forall Γ' Δ', Permutation Γ Γ' -> Permutation Δ Δ' -> seq Γ' Δ'.
Proof.
  induction Seq; intros Γ' Δ' PermΓ PermΔ;
    try destruct (perm_elem PermΓ) as [ΓL [ΓR [-> PermΓLR]]];
    try destruct (perm_elem PermΔ) as [ΔL [ΔR [-> PermΔLR]]];
    try solve [
      constructor;
      match goal with [ H : _ |- _ ] => apply H; solve [repeat apply perm_inside; auto] end].
  - apply prod_sub; auto using perm_filter_field.
  - apply fn_sub; auto using perm_filter_field.
Qed.

Ltac find_prefix pfx_r x xs :=
  match xs with
  | x :: _ => apply (Permutation_cons_app (rev pfx_r)); simpl
  | ?y :: ?ys => find_prefix (cons y pfx_r) x ys
  end.

Ltac auto_perm :=
  repeat match goal with
  | [ |- Permutation ?e ?e ] => apply Permutation_refl
  | [ |- Permutation (?x :: ?xs) ?ys ] => find_prefix (nil : list term) x ys
  end.

Lemma swapΓ {Γ Δ A B} : seq (A :: B :: Γ) Δ -> seq (B :: A :: Γ) Δ.
intro H; apply (permutation H); auto_perm. Qed.

Lemma swapΔ {Γ Δ A B} : seq Γ (A :: B :: Δ) -> seq Γ (B :: A :: Δ).
intro H; apply (permutation H); auto_perm. Qed.




Definition starts {A : Set} (x : A) (xs : list A) : Prop :=
  match xs with cons x' _ => x = x' | nil => False end.

Ltac starts_app :=
  match goal with
  | [ H : starts _ (?a ++ _) |- _ ] =>
    destruct a; simpl in *; try discriminate H; try (injection H as; subst)
  | [ H : starts _ ?a |- _ ] =>
    destruct a; simpl in *; try contradiction
  end.

Fact starts_dep {A : Set} {P : list A -> Prop} {x : A} :
  (forall xs, starts x xs -> P xs) <-> (forall xs, P (x :: xs)).
split; intros H xs; [apply H | intro S; starts_app; subst]; simpl; auto. Qed.

Definition ForConsSubterms (P : term -> list term -> list term -> Prop) (X : term) :=
  match X with
  | prod X1 X2 => forall Γ Δ, (seq (X1 :: Γ) Δ -> P X1 Γ Δ) /\ (seq (X2 :: Γ) Δ -> P X2 Γ Δ)
  | fn X1 X2 => forall Γ Δ, P X1 Γ Δ /\ P X2 Γ Δ
  | _ => True
  end.
Arguments ForConsSubterms P !X.

Lemma seq_XΓ_Δ_ind
  (P : term -> list term -> list term -> Prop)
  (* inactive *)
  (P_hyp : forall X Γ₁ Γ₂ Δ₁ Δ₂ v, P X (Γ₁ ++ var v :: Γ₂) (Δ₁ ++ var v :: Δ₂))
  (P_meet_l : forall X Γ₁ Γ₂ Δ A B, P X (Γ₁ ++ A :: B :: Γ₂) Δ -> P X (Γ₁ ++ meet A B :: Γ₂) Δ)
  (P_meet_r : forall X Γ Δ₁ Δ₂ A B, P X Γ (Δ₁ ++ A :: Δ₂) -> P X Γ (Δ₁ ++ B :: Δ₂) -> P X Γ (Δ₁ ++ meet A B :: Δ₂))
  (P_join_l : forall X Γ₁ Γ₂ Δ A B, P X (Γ₁ ++ A :: Γ₂) Δ -> P X (Γ₁ ++ B :: Γ₂) Δ -> P X (Γ₁ ++ join A B :: Γ₂) Δ)
  (P_join_r : forall X Γ Δ₁ Δ₂ A B, P X Γ (Δ₁ ++ A :: B :: Δ₂) -> P X Γ (Δ₁ ++ join A B :: Δ₂))
  (P_bot_l : forall X Γ₁ Γ₂ Δ, P X (Γ₁ ++ bot :: Γ₂) Δ)
  (P_top_r : forall X Γ Δ₁ Δ₂, P X Γ (Δ₁ ++ top :: Δ₂))
  (* active (left rules only) *)
  (P_hyp_X : forall v Γ Δ₁ Δ₂, P (var v) Γ (Δ₁ ++ var v :: Δ₂))
  (P_join_X : forall A B Γ Δ, seq (A :: Γ) Δ -> P A Γ Δ -> seq (B :: Γ) Δ -> P B Γ Δ -> P (join A B) Γ Δ)
  (P_meet_X : forall A B Γ Δ,
      seq (A :: B :: Γ) Δ ->
      (forall Γ' Δ', seq (A :: Γ') Δ' -> P A Γ' Δ') ->
      (forall Γ' Δ', seq (B :: Γ') Δ' -> P B Γ' Δ') ->
      P (meet A B) Γ Δ)
  (P_bot_X : forall Γ Δ, P bot Γ Δ)
  (* constructed terms *)
  (P_prod_sub : forall X Γ Δ, 
      seq (filter_field f_left (X :: Γ)) (filter_field f_left Δ) ->
      seq (filter_field f_right (X :: Γ)) (filter_field f_right Δ) ->
      P X Γ Δ)
  (P_fn_sub : forall X Γ Δ,
      seq (filter_field f_dom Δ) (filter_field f_dom (X :: Γ)) ->
      seq (filter_field f_range (X :: Γ)) (filter_field f_range Δ) ->
      P X Γ Δ)
  : forall X Γ Δ, seq (X :: Γ) Δ -> P X Γ Δ.
Proof.
  intro X.
  cut (forall Γ', starts X Γ' -> forall Δ, seq Γ' Δ -> P X (tl Γ') Δ).
  intro H; apply ((proj1 starts_dep) H).
  induction X; intros Γ' StartX Δ; induction 1; try starts_app; auto;
    try solve [subst;
               (apply P_prod_sub; simpl; auto; discriminate)
             ||(apply P_fn_sub; simpl; auto; discriminate)];
  try pose (IHX1' := proj1 starts_dep IHX1); simpl in IHX1';
  try pose (IHX2' := proj1 starts_dep IHX2); simpl in IHX2';
    subst; auto; simpl in *.
Qed.

Lemma seq_Γ_XΔ_ind
  (P : term -> list term -> list term -> Prop)
  (* inactive *)
  (P_hyp : forall X Γ₁ Γ₂ Δ₁ Δ₂ v, P X (Γ₁ ++ var v :: Γ₂) (Δ₁ ++ var v :: Δ₂))
  (P_meet_l : forall X Γ₁ Γ₂ Δ A B, P X (Γ₁ ++ A :: B :: Γ₂) Δ -> P X (Γ₁ ++ meet A B :: Γ₂) Δ)
  (P_meet_r : forall X Γ Δ₁ Δ₂ A B, P X Γ (Δ₁ ++ A :: Δ₂) -> P X Γ (Δ₁ ++ B :: Δ₂) -> P X Γ (Δ₁ ++ meet A B :: Δ₂))
  (P_join_l : forall X Γ₁ Γ₂ Δ A B, P X (Γ₁ ++ A :: Γ₂) Δ -> P X (Γ₁ ++ B :: Γ₂) Δ -> P X (Γ₁ ++ join A B :: Γ₂) Δ)
  (P_join_r : forall X Γ Δ₁ Δ₂ A B, P X Γ (Δ₁ ++ A :: B :: Δ₂) -> P X Γ (Δ₁ ++ join A B :: Δ₂))
  (P_bot_l : forall X Γ₁ Γ₂ Δ, P X (Γ₁ ++ bot :: Γ₂) Δ)
  (P_top_r : forall X Γ Δ₁ Δ₂, P X Γ (Δ₁ ++ top :: Δ₂))
  (* active (right rules only) *)
  (P_hyp_X : forall v Γ₁ Γ₂ Δ, P (var v) (Γ₁ ++ var v :: Γ₂) Δ)
  (P_join_X : forall A B Γ Δ, seq Γ (A :: B :: Δ) -> P A Γ (B :: Δ) -> P (join A B) Γ Δ)
  (P_meet_X : forall A B Γ Δ,
      seq Γ (A :: Δ) -> seq Γ (B :: Δ) ->
      (forall Γ' Δ', seq Γ' (A :: Δ') -> P A Γ' Δ') ->
      (forall Γ' Δ', seq Γ' (B :: Δ') -> P B Γ' Δ') ->
      P (meet A B) Γ Δ)
  (P_top_X : forall Γ Δ, P top Γ Δ)
  (* constructed terms *)
  (P_prod_sub : forall X Γ Δ, 
      seq (filter_field f_left Γ) (filter_field f_left (X :: Δ)) ->
      seq (filter_field f_right Γ) (filter_field f_right (X :: Δ)) ->
      P X Γ Δ)
  (P_fn_sub : forall X Γ Δ,
      seq (filter_field f_dom (X :: Δ)) (filter_field f_dom Γ) ->
      seq (filter_field f_range Γ) (filter_field f_range (X :: Δ)) ->
      P X Γ Δ)
  : forall X Δ Γ, seq Γ (X :: Δ) -> P X Γ Δ.
Proof.
  intro X.
  cut (forall Δ', starts X Δ' -> forall Γ, seq Γ Δ' -> P X Γ (tl Δ')).
  intro H; apply ((proj1 starts_dep) H).
  induction X; intros Δ' StartX Γ; induction 1; try starts_app; auto;
    try solve [subst;
               (apply P_prod_sub; simpl; auto; discriminate)
             ||(apply P_fn_sub; simpl; auto; discriminate)];
  try pose (IHX1' := proj1 starts_dep IHX1); simpl in IHX1';
  try pose (IHX2' := proj1 starts_dep IHX2); simpl in IHX2';
    subst; auto; simpl in *.
Qed.

Ltac seq_induction A :=
  match type of A with
  | seq (?X :: ?Γ) ?Δ =>
    pattern X, Γ, Δ; apply seq_XΓ_Δ_ind; try assumption; clear X Γ Δ A; intros
  | seq ?Γ (?X :: ?Δ) =>
    pattern X, Γ, Δ; apply seq_Γ_XΔ_ind; try assumption; clear X Γ Δ A; intros
  end.

Ltac fold_seq :=
  repeat match goal with
  | [ |- context [ ?a :: ?b ++ ?c ] ] => replace (a :: b ++ c) with ((a :: b) ++ c) by reflexivity
  | [ |- seq (?h :: ?t) _ ] => replace (h :: t) with (nil ++ h :: t) by reflexivity
  | [ |- seq _ (?h :: ?t) ] => replace (h :: t) with (nil ++ h :: t) by reflexivity
  end.


Lemma invert_Γ X : forall {Γ Δ}, seq (X :: Γ) Δ ->
  match X with
  | join A B => seq (A :: Γ) Δ /\ seq (B :: Γ) Δ
  | meet A B => seq (A :: B :: Γ) Δ
  | top => seq Γ Δ
  | _ => True
  end.
Proof.
  intros Γ Δ Seq. seq_induction Seq; auto;
    destruct X; firstorder; repeat rewrite app_comm_cons; try solve [seqrule | simpl in *; repeat apply weak1; solve [seqrule_prod | seqrule_fn]].
Qed.

Lemma invert_Δ X : forall {Γ Δ}, seq Γ (X :: Δ) ->
  match X with
  | join A B => seq Γ (A :: B :: Δ)
  | meet A B => seq Γ (A :: Δ) /\ seq Γ (B :: Δ)
  | bot => seq Γ Δ
  | _ => True
  end.
Proof.
  intros Γ Δ Seq. seq_induction Seq; auto;
    destruct X; firstorder; repeat rewrite app_comm_cons; try solve [seqrule | simpl in *; repeat apply weak1; solve [seqrule_prod | seqrule_fn]].
Qed.

(*

Contraction for ∧:

If
   A, B, A ∧ B, Γ ⊢ Δ
then
   A, B, A, B, Γ ⊢ Δ

If A, B, Γ ⊢ Δ
then

*)

Definition ContractionΓ (X : term) : Prop :=
  forall {Γ Δ} (Seq : seq (X :: Γ) Δ) (StartX : starts X Γ), seq Γ Δ.
Definition ContractionΔ (X : term) : Prop :=
  forall {Γ Δ} (Seq : seq Γ (X :: Δ)) (StartX : starts X Δ), seq Γ Δ.

Lemma contraction_Γ_var {v} : ContractionΓ (var v).
Proof.
  intros Γ Δ Seq. remember (var v) as X. revert HeqX.
  seq_induction Seq; starts_app; subst;
    try discriminate; try injection StartX as; subst;
    try (repeat rewrite shift'; seqrule; simpl); auto.
  - rewrite shift_nil. seqrule.
  - injection HeqX as. subst. rewrite shift_nil. seqrule.
  - apply prod_sub; simpl; auto.
  - apply fn_sub; simpl; auto.
Qed.

Lemma contraction_Δ_var {v} : ContractionΔ (var v).
Proof.
  intros Γ Δ Seq. remember (var v) as X. revert HeqX.
  seq_induction Seq; starts_app; subst;
    try discriminate; try injection StartX as; subst;
      try (fold_seq; seqrule; simpl; auto).
  - apply prod_sub; simpl; auto.
  - apply fn_sub; simpl; auto.
Qed.

Lemma contraction_Γ_prod {P Q} (ContP : ContractionΓ P) (ContQ : ContractionΓ Q) : ContractionΓ (prod P Q).
Proof.
  intros Γ Δ Seq. remember (prod P Q) as X. revert HeqX.
  seq_induction Seq; starts_app; repeat (progress subst); try discriminate;
    try (fold_seq; seqrule; simpl; auto).
  - apply prod_sub; simpl; [apply ContP | apply ContQ]; simpl; auto.
  - apply fn_sub; simpl; auto.
Qed.

Lemma contraction_Δ_prod {P Q} (ContP : ContractionΔ P) (ContQ : ContractionΔ Q) : ContractionΔ (prod P Q).
Proof.
  intros Γ Δ Seq. remember (prod P Q) as X. revert HeqX.
  seq_induction Seq; starts_app; repeat (progress subst); try discriminate;
    try (fold_seq; seqrule; simpl; auto).
  - apply prod_sub; simpl; [apply ContP | apply ContQ]; simpl; auto.
  - apply fn_sub; simpl; auto.
Qed.

Lemma contraction_Γ_fn {P Q} (ContP : ContractionΔ P) (ContQ : ContractionΓ Q) : ContractionΓ (fn P Q).
Proof.
  intros Γ Δ Seq. remember (fn P Q) as X. revert HeqX.
  seq_induction Seq; starts_app; repeat (progress subst); try discriminate;
    try (fold_seq; seqrule; simpl; auto).
  - apply prod_sub; simpl; auto.
  - apply fn_sub; simpl;  [apply ContP | apply ContQ]; simpl; auto.
Qed.

Lemma contraction_Δ_fn {P Q} (ContP : ContractionΓ P) (ContQ : ContractionΔ Q) : ContractionΔ (fn P Q).
Proof.
  intros Γ Δ Seq. remember (fn P Q) as X. revert HeqX.
  seq_induction Seq; starts_app; repeat (progress subst); try discriminate;
    try (fold_seq; seqrule; simpl; auto).
  - apply prod_sub; simpl; auto.
  - apply fn_sub; simpl;  [apply ContP | apply ContQ]; simpl; auto.
Qed.

Theorem contraction_ΓΔ A : ContractionΓ A /\ ContractionΔ A.
Proof.
  induction A; intros.
  - split; auto using contraction_Γ_var, contraction_Δ_var.
  - split; intros Γ Δ Seq StartX; starts_app; repeat (progress subst).
    * fold_seq; seqrule_prim; [apply (proj1 IHA1) | apply (proj1 IHA2)]; simpl; auto;
      apply (invert_Γ (join A1 A2)); apply swapΓ; apply (invert_Γ (join A1 A2)); auto.
    * fold_seq; seqrule_prim; simpl.
      apply (proj2 IHA1); simpl; auto. apply (@permutation Γ (A2 :: A1 :: A1 :: Δ)); try auto_perm.
      apply (proj2 IHA2); simpl; auto. apply (@permutation Γ (A1 :: A2 :: A1 :: A2 :: Δ)); try auto_perm.
      apply (invert_Δ (join A1 A2)). apply (@permutation Γ (A1 :: A2 :: join A1 A2 :: Δ)); try auto_perm.
      apply (invert_Δ (join A1 A2)); assumption.
  - split; intros Γ Δ Seq StartX; starts_app; repeat (progress subst).
    * fold_seq; seqrule_prim; simpl.
      apply (proj1 IHA1); simpl; auto. apply (@permutation (A2 :: A1 :: A1 :: Γ) Δ); try auto_perm.
      apply (proj1 IHA2); simpl; auto. apply (@permutation (A1 :: A2 :: A1 :: A2 :: Γ) Δ); try auto_perm.
      apply (invert_Γ (meet A1 A2)). apply (@permutation (A1 :: A2 :: meet A1 A2 :: Γ) Δ); try auto_perm.
      apply (invert_Γ (meet A1 A2)). assumption.
    * fold_seq; seqrule_prim; simpl; [apply (proj2 IHA1) | apply (proj2 IHA2)]; simpl; auto;
        apply (invert_Δ (meet A1 A2)); apply swapΔ; apply (invert_Δ (meet A1 A2)); auto.
  - split; intros Γ Δ Seq StartX; starts_app; repeat (progress subst).
    apply (invert_Γ top); auto.
    fold_seq; seqrule.
  - split; intros Γ Δ Seq StartX; starts_app; repeat (progress subst).
    fold_seq; seqrule.
    apply (invert_Δ bot); auto.
  - split; [ apply contraction_Γ_prod | apply contraction_Δ_prod ]; intuition.
  - split; [ apply contraction_Γ_fn | apply contraction_Δ_fn ]; intuition.
Qed.

Fact contraction_Γ A : forall {Γ Δ}, seq (A :: A :: Γ) Δ -> seq (A :: Γ) Δ.
Proof. intros; apply (proj1 (contraction_ΓΔ A)); simpl; auto. Qed.

Fact contraction_Δ A : forall {Γ Δ}, seq Γ (A :: A :: Δ) -> seq Γ (A :: Δ).
Proof. intros; apply (proj2 (contraction_ΓΔ A)); simpl; auto. Qed.

(*

If A ∧ B, A ∧ B, Γ ⊢ Δ
perhaps
   A, B, A ∧ B, Γ ⊢ Δ
then invert, done

but perhaps

   A ∧ B, A, B, Γ ⊢ Δ

in which case we don't have an A, B IH nor a starts.

If A × B, A × B, Γ ⊢ Δ
perhaps
   A, A, Γ ⊢ Δ
or else something not affecting A
Noice.
Fuck it, do it live.

Why is contraction true for e.g. meet?

If A ∧ B, A ∧ B, Γ ⊢ Δ
then by inversion (twice)
   A, B, A, B, Γ ⊢ Δ
then swap/contract

If A → B, A → B, Γ ⊢ Δ
then remember, induct. Not affected until all affected.

Do this by induction on the *term* and inversion principles.

*)

Lemma contractionNΓ : forall Γ Γ' Δ, seq (Γ ++ Γ ++ Γ') Δ -> seq (Γ ++ Γ') Δ.
Proof.
  induction Γ as [| A Γ]; intros Γ' Δ H; simpl in *; auto.
  apply (@permutation (Γ ++ A :: Γ') Δ). apply IHΓ. apply (@permutation (A :: Γ ++ Γ ++ Γ') Δ). apply contraction_Γ.
  apply (@permutation (A :: Γ ++ A :: Γ ++ Γ') Δ); auto.
  auto_perm. Search Permutation. fold_seq. do 2 rewrite app_assoc. auto using Permutation_app, Permutation_app_comm.
  do 2 rewrite app_assoc. auto using Permutation_middle.
  auto using Permutation_refl. auto using Permutation_sym, Permutation_middle. auto using Permutation_refl.
Qed.

Lemma contractionNΔ : forall Δ Δ' Γ, seq Γ (Δ ++ Δ ++ Δ') -> seq Γ (Δ ++ Δ').
Proof.
  induction Δ as [| A Δ]; intros Δ' Γ H; simpl in *; auto.
  apply (@permutation Γ (Δ ++ A :: Δ')); auto using Permutation_refl, Permutation_sym, Permutation_middle.
  apply IHΔ.
  apply (@permutation Γ (A :: (Δ ++ Δ) ++ Δ')); try rewrite app_assoc; auto using Permutation_middle, Permutation_refl.
  apply contraction_Δ.
  apply (@permutation Γ (A :: Δ ++ A :: Δ ++ Δ')); auto using Permutation_refl.
  fold_seq. rewrite app_assoc. apply Permutation_app; auto using Permutation_refl.
  simpl. apply Permutation_cons; auto. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma contractionN : forall {Γ Δ Γ' Δ'}, seq (Γ ++ Γ ++ Γ') (Δ ++ Δ ++ Δ') -> seq (Γ ++ Γ') (Δ ++ Δ').
Proof. intros. apply contractionNΓ. apply contractionNΔ. assumption. Qed.

Definition Cut (X : term) := forall Γ Δ, seq (X :: Γ) Δ -> forall Γ' Δ', seq Γ' (X :: Δ') -> seq (Γ ++ Γ') (Δ ++ Δ').


Lemma cut_prod {A B} (CutA : Cut A) (CutB : Cut B) : Cut (prod A B).
Proof.
  intros Γ Δ Seq.
  remember (prod A B) as X; revert HeqX; seq_induction Seq;
    try discriminate HeqX; subst; simpl in *;
    try (seqrule; auto).
  - remember (prod A B) as X; revert HeqX; seq_induction H1;
    try discriminate HeqX; subst; simpl in *;
    try (seqrule; auto).
    * apply prod_sub; repeat rewrite filter_field_app; auto.
    * apply weakN; apply fn_sub; auto.
  - apply (@permutation (Γ' ++ Γ) (Δ' ++ Δ)); try apply Permutation_app_comm.
    apply weakN; apply fn_sub; repeat rewrite filter_field_app; auto.
Qed.

Fact swap_app {Γ Δ Γ' Δ'} : seq (Γ ++ Γ') (Δ ++ Δ') -> seq (Γ' ++ Γ) (Δ' ++ Δ).
intro H. apply (@permutation (Γ ++ Γ') (Δ ++ Δ')); try apply Permutation_app_comm. auto. Qed.

Lemma cut_fn {A B} (CutA : Cut A) (CutB : Cut B) : Cut (fn A B).
Proof.
  intros Γ Δ Seq.
  remember (fn A B) as X; revert HeqX; seq_induction Seq;
    try discriminate HeqX; subst; simpl in *;
    try (seqrule; auto).
  - apply (@permutation (Γ' ++ Γ) (Δ' ++ Δ)); try apply Permutation_app_comm.
    apply weakN; apply prod_sub; repeat rewrite filter_field_app; auto.
  - remember (fn A B) as X; revert HeqX; seq_induction H1;
    try discriminate HeqX; subst; simpl in *;
    try (seqrule; auto).
    * apply weakN; apply prod_sub; repeat rewrite filter_field_app; auto.
    * apply fn_sub; repeat rewrite filter_field_app; auto using swap_app.
Qed.

Lemma cut_var {v} : Cut (var v).
  intros Γ Δ Seq.
  remember (var v) as X; revert HeqX; seq_induction Seq;
  try discriminate HeqX; subst; simpl in *;
  try (seqrule; auto).
  - injection HeqX as; subst.
    remember (var v) as X; revert HeqX; seq_induction H;
    try discriminate HeqX; subst; simpl in *;
    try (seqrule; auto).
    * rewrite app_prefix. rewrite app_suffix. seqrule.
    * apply weakN. apply prod_sub; auto.
    * apply weakN. apply fn_sub; auto.
  - apply swap_app. apply weakN. apply prod_sub; auto.
  - apply swap_app. apply weakN. apply fn_sub; auto.
Qed.

Theorem cut : forall X, Cut X.
Proof.
  induction X; try auto using cut_var, cut_prod, cut_fn;
  match goal with
  [ |- Cut ?t ] => intros Γ Δ Seq Γ' Δ' Seq'; apply (invert_Γ t) in Seq; apply (invert_Δ t) in Seq'
  end.
  - apply contractionN. apply IHX2; try tauto.
    apply (@permutation (Γ ++ Γ') (Δ, [X2], Δ')); try auto_perm.
    apply IHX1; tauto. apply Permutation_sym. apply Permutation_middle. (* FIXME: better autoperm *)
  - apply swap_app. apply contractionN. do 2 rewrite app_assoc. apply swap_app. do 2 rewrite app_assoc.
    apply IHX2; try tauto.
    fold_seq. apply IHX1; tauto.
  - apply swap_app. apply weakN; auto.
  - apply weakN; auto.
Qed.

(*
    Active join, cut on both sides.

A, Γ ⊢ Δ
B, Γ ⊢ Δ
 ---
A ∨ B, Γ ⊢ Δ

Γ' ⊢ Δ', A, B
 ---
Γ' ⊢ Δ', A ∨ B


Have
  B, Γ ⊢ Δ
  Γ' ⊢ (Δ', A), B
Cut IH at B:
  Γ, Γ' ⊢ Δ, Δ', A
Have:
  Γ, Γ' ⊢ Δ', A
  A, Γ  ⊢ Δ
Cut gives:
  Γ, Γ, Γ' ⊢ Δ', Δ
Need contraction here.

Active meet.

A ∧ B, Γ ⊢ Δ
Γ' ⊢ A ∧ B, Δ'



*)

Lemma consistent : ~ (seq nil nil).
Proof.
  cut (forall {Γ Δ}, seq Γ Δ -> Γ = nil -> Δ = nil -> False); try solve [firstorder].
  intros Γ Δ Seq; induction Seq; intros H1 H2;
  try match goal with [ H : ?Γ, [_], _ = nil |- _ ] => destruct Γ; discriminate H end;
  subst; simpl in *; auto.
Qed.

Lemma seq_inversion {Γ Δ} {A B : term} :
  Γ , [A], Δ = B :: nil -> A = B.
Proof.
  destruct Γ; destruct Δ; intro H; try discriminate H; injection H as; auto; destruct Γ; discriminate.
Qed.

Notation "A ≤ B" := (seq (A :: nil) (B :: nil)) (at level 40).

Ltac sub_inversion X :=
  inversion X; repeat (
    simpl in *;
    match goal with
    | [ H : seq nil nil |- _ ] => solve [exfalso; exact (consistent H)]
    | [ H : _ |- _ ] =>
      apply seq_inversion in H;
      try (discriminate H || injection H as);
      subst
    end); simpl in *.

Fact sub_inversion_var {v v'} : var v ≤ var v' -> v = v'.
intro H; sub_inversion H; auto. Qed.

Fact sub_inversion_fn {A B A' B'} : fn A B ≤ fn A' B' -> A' ≤ A /\ B ≤ B'.
intro H; sub_inversion H; auto. Qed.

Fact sub_inversion_prod {A B A' B'} : prod A B ≤ prod A' B' -> A ≤ A' /\ B ≤ B'.
intro H; sub_inversion H; auto. Qed.

Fact reflexive {A} : A ≤ A.
exact (@refl A nil nil nil nil). Qed.

Fact transitive {A B C} : A ≤ B -> B ≤ C -> A ≤ C.
intros Hab Hbc. cut (seq (nil ++ (A :: nil)) ((C :: nil) ++ nil)); auto. apply (cut B); auto. Qed.

