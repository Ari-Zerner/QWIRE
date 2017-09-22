Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.

(*** Context Definitions ***)

(** Types **)
Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.
Notation " W1 ⊗ W2 " := (Tensor W1 W2) (at level 40, left associativity)
                     : circ_scope.

Open Scope circ_scope.
Fixpoint size_WType (W : WType) : nat := 
  match W with
  | One => 0
  | Qubit => 1
  | Bit => 1
  | W1 ⊗ W2 => size_WType W1 + size_WType W2
  end.

(* Coq interpretations of wire types *)
Fixpoint interpret (w:WType) : Set :=
  match w with
    | Qubit => bool
    | Bit   => bool 
    | One   => unit
    | w1 ⊗ w2 => (interpret w1) * (interpret w2)
  end.
Close Scope circ_scope.


(** Variables **)
Definition Var := nat.
Definition Ctx := list (option WType).

Inductive OCtx := 
| Invalid : OCtx 
| Valid : Ctx -> OCtx.

(* The size of a context is the number of wires it holds *)
Fixpoint size_Ctx (Γ : Ctx) : nat :=
  match Γ with
  | [] => 0
  | None :: Γ' => size_Ctx Γ'
  | Some _ :: Γ' => S (size_Ctx Γ')
  end.
Definition size_OCtx (Γ : OCtx) : nat :=
  match Γ with
  | Invalid => 0
  | Valid Γ' => size_Ctx Γ'
  end.


Lemma ctx_octx : forall Γ Γ', Valid Γ = Valid Γ' <-> Γ = Γ'.
Proof. intuition; congruence. Defined.

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w, SingletonCtx 0 w [Some w]
| SingletonLater : forall x w Γ, SingletonCtx x w Γ -> SingletonCtx (S x) w (None::Γ)
.

Fixpoint singleton (x : Var) (W : WType) : Ctx :=
  match x with
  | O => [Some W]
  | S x => None :: singleton x W
  end.

Lemma singleton_singleton : forall x W,
      SingletonCtx x W (singleton x W).
Proof.
  induction x; intros W.
  - constructor. 
  - simpl. constructor. apply IHx.
Defined.   

Lemma singleton_equiv : forall x W Γ,
      SingletonCtx x W Γ -> Γ = singleton x W.
Proof.
  induction 1; trivial.
  simpl. rewrite IHSingletonCtx. reflexivity.
Defined.


Definition merge_wire (o1 o2 : option WType) : OCtx :=
  match o1, o2 with
  | None, o2 => Valid [o2]
  | Some w1, None => Valid [Some w1]
  | _, _ => Invalid
  end.

Fixpoint merge' (Γ1 Γ2 : Ctx) : OCtx :=
  match Γ1, Γ2 with
  | [], _ => Valid Γ2
  | _, [] => Valid Γ1
  | o1 :: Γ1', o2 :: Γ2' => match merge_wire o1 o2 with
                           | Invalid => Invalid
                           | Valid Γ0 => match merge' Γ1' Γ2' with
                                        | Invalid => Invalid
                                        | Valid Γ' => Valid (Γ0 ++ Γ')
                                        end
                           end
  end.                            

Definition merge (Γ1 Γ2 : OCtx) : OCtx :=
  match Γ1, Γ2 with
  | Valid Γ1', Valid Γ2' => merge' Γ1' Γ2'
  | _, _ => Invalid
  end. 

Notation "∅" := (Valid []).
Infix "⋓" := merge (left associativity, at level 50).
Coercion Valid : Ctx >-> OCtx.

(*** Facts about ⋓ ***)


Lemma merge_merge' : forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = (merge' Γ1 Γ2).
Proof. reflexivity. Defined.

(* Note that the reverse is not always true - we would need to 
   check validity and not-emptyness of the contexts *)
Lemma merge_cancel_l : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ ⋓ Γ1 = Γ ⋓ Γ2.
Proof. intros; subst; reflexivity. Defined.

Lemma merge_cancel_r : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ1 ⋓ Γ = Γ2 ⋓ Γ.
Proof. intros; subst; reflexivity. Defined.

Lemma merge_I_l : forall Γ, Invalid ⋓ Γ = Invalid. Proof. reflexivity. Defined.

Lemma merge_I_r : forall Γ, Γ ⋓ Invalid = Invalid. Proof. destruct Γ; reflexivity.
Defined.

(*
Lemma merge_valid : forall (Γ1 Γ2 : OCtx) (Γ : Ctx), 
  Γ1 ⋓ Γ2 = Valid Γ ->
  (exists Γ1', Γ1 = Valid Γ1') /\ (exists Γ2', Γ2 = Valid Γ2'). 
Proof.
  intros Γ1 Γ2 Γ M.
  destruct Γ1 as [|Γ1'], Γ2 as [|Γ2']; inversion M.
  eauto.
Qed.
*)

Lemma merge_valid : forall (Γ1 Γ2 : OCtx) (Γ : Ctx), 
  Γ1 ⋓ Γ2 = Valid Γ ->
  {Γ1' : Ctx & Γ1 = Valid Γ1'} * {Γ2' : Ctx & Γ2 = Valid Γ2'}. 
Proof.
  intros Γ1 Γ2 Γ M.
  destruct Γ1 as [|Γ1'], Γ2 as [|Γ2']; inversion M.
  eauto.
Defined.

Lemma merge_invalid_iff : forall (o1 o2 : option WType) (Γ1 Γ2 : Ctx), 
  Valid (o1 :: Γ1) ⋓ Valid (o2 :: Γ2) = Invalid <-> 
  merge_wire o1 o2 = Invalid \/ Γ1 ⋓ Γ2 = Invalid.
Proof.
  intros o1 o2 Γ1 Γ2.
  split.  
  + intros H.
    destruct o1, o2; auto; right; simpl in H.    
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
  + intros H.
    inversion H.
    simpl. rewrite H0; reflexivity.
    simpl.
    destruct (merge_wire o1 o2); trivial.
    rewrite merge_merge' in H0.
    rewrite H0.
    reflexivity.
Defined.

Lemma merge_nil_l : forall Γ, ∅ ⋓ Γ = Γ. Proof. destruct Γ; reflexivity. Defined.

Lemma merge_nil_r : forall Γ, Γ ⋓ ∅ = Γ. 
Proof. destruct Γ; trivial. destruct c; trivial. Defined. 

Lemma merge_comm : forall Γ1 Γ2, Γ1 ⋓ Γ2 = Γ2 ⋓ Γ1. 
Proof.
  intros Γ1 Γ2.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; trivial.
  generalize dependent Γ2.
  induction Γ1. 
  + destruct Γ2; trivial.
  + destruct Γ2; trivial.
    simpl.
    unfold merge in IHΓ1. 
    rewrite IHΓ1.
    destruct a, o; reflexivity.
Defined.    

Lemma merge_assoc : forall Γ1 Γ2 Γ3, Γ1 ⋓ (Γ2 ⋓ Γ3) = Γ1 ⋓ Γ2 ⋓ Γ3. 
Proof.
  intros Γ1 Γ2 Γ3.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2], Γ3 as [|Γ3]; repeat (rewrite merge_I_r); trivial.
  generalize dependent Γ3. generalize dependent Γ1.
  induction Γ2 as [| o2 Γ2']. 
  + intros. rewrite merge_nil_l, merge_nil_r; reflexivity.
  + intros Γ1 Γ3.
    destruct Γ1 as [|o1 Γ1'], Γ3 as [| o3 Γ3'] ; trivial.
    - rewrite 2 merge_nil_l.
      reflexivity.
    - rewrite 2 merge_nil_r.
      reflexivity.
    - destruct o1, o2, o3; trivial.
      * simpl. destruct (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2'), (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2'), (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
Defined.



Definition cons_o (o : option WType) (Γ : OCtx) : OCtx :=
  match Γ with
  | Invalid => Invalid
  | Valid Γ' => Valid (o :: Γ')
  end.

Lemma cons_distr_merge : forall Γ1 Γ2,
  cons_o None (Γ1 ⋓ Γ2) = cons_o None Γ1 ⋓ cons_o None Γ2.
Proof. destruct Γ1; destruct Γ2; simpl; auto. Defined.

Lemma merge_nil_inversion' : forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = ∅ -> (Γ1 = []) * (Γ2 = []).
Proof.
  induction Γ1 as [ | o Γ1]; intros Γ2; try inversion 1; auto.
  destruct Γ2 as [ | o' Γ2]; try solve [inversion H1].
  destruct o, o', (merge' Γ1 Γ2); inversion H1. 
Defined.

Lemma merge_nil_inversion : forall (Γ1 Γ2 : OCtx), Γ1 ⋓ Γ2 = ∅ -> (Γ1 = ∅) * (Γ2 = ∅).
Proof.
  intros Γ1 Γ2 eq.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try solve [inversion eq].
  apply merge_nil_inversion' in eq.
  intuition; congruence.
Defined.

(* This is false. Needs an assumption that Γ1 ≠ ∅ ≠ Γ2 
Lemma ctx_cons_inversion : forall Γ1 Γ2 o Γ,
      Γ1 ⋓ Γ2 = Valid (o :: Γ) ->
      {o1 : option WType & {o2 : option WType & {Γ1' : Ctx & {Γ2' : Ctx 
      & (Γ1 = Valid (o1 :: Γ1')) * (Γ2 = Valid (o2 :: Γ2')) * (Γ1' ⋓ Γ2' = Valid Γ)
        * (merge_wire o1 o2 = Valid [o])}}}}%type.
*)

Lemma ctx_cons_inversion : forall (Γ Γ1 Γ2 : Ctx) o o1 o2,
      Valid (o1 :: Γ1) ⋓ Valid (o2 :: Γ2) = Valid (o :: Γ) ->
      (Γ1 ⋓ Γ2 = Valid Γ) * (merge_wire o1 o2 = Valid [o]).
Proof.
  intros Γ Γ1 Γ2 o o1 o2 H.
  inversion H.
  destruct (merge_wire o1 o2) eqn:Eq1. inversion H1.
  rewrite <- merge_merge' in H1.
  destruct (Γ1 ⋓ Γ2) eqn:Eq2. inversion H1.
  destruct o1, o2; simpl in Eq1. inversion Eq1.
  - apply ctx_octx in Eq1. rewrite <- Eq1 in *.
    simpl in H1.
    inversion H1; subst; auto.
  - apply ctx_octx in Eq1. rewrite <- Eq1 in *.
    simpl in H1.
    inversion H1; subst; auto.
  - apply ctx_octx in Eq1. rewrite <- Eq1 in *.
    simpl in H1.
    inversion H1; subst; auto.
Defined.

(*** Validity ***)

Definition is_valid (Γ : OCtx) : Prop := exists Γ', Γ = Valid Γ'.

Lemma valid_valid : forall Γ, is_valid (Valid Γ). Proof. intros. exists Γ. reflexivity. Defined.

Lemma valid_empty : is_valid ∅. Proof. unfold is_valid; eauto. Defined.

Lemma not_valid : not (is_valid Invalid). Proof. intros [Γ F]; inversion F. Defined.

Lemma valid_split_basic : forall Γ1 Γ2, is_valid (Γ1 ⋓ Γ2) -> is_valid Γ1 /\ is_valid Γ2.
Proof.
  intros Γ1 Γ2 V.
  unfold is_valid in *.
  destruct V as [Γ' V].
  apply merge_valid in V as [[Γ1'] [Γ2']].
  eauto.
Defined.

Lemma valid_cons : forall (o1 o2 : option WType) (Γ1 Γ2 : Ctx), 
  is_valid (Valid (o1 :: Γ1) ⋓ Valid (o2 :: Γ2)) <-> 
  (is_valid (merge_wire o1 o2) /\ is_valid (Γ1 ⋓ Γ2)).
Proof.
  intros o1 o2 Γ1 Γ2. split.
  - intros [Γ V].
    inversion V.
    destruct (merge_wire o1 o2). inversion H0.
    simpl. destruct (merge' Γ1 Γ2). inversion H0.
    unfold is_valid; split; eauto.
  - intros [[W Vo] [Γ V]].
    simpl in *.
    rewrite Vo, V.
    unfold is_valid; eauto.
Defined.


Lemma valid_join : forall Γ1 Γ2 Γ3, is_valid (Γ1 ⋓ Γ2) -> is_valid (Γ1 ⋓ Γ3) -> is_valid (Γ2 ⋓ Γ3) -> 
                               is_valid (Γ1 ⋓ Γ2 ⋓ Γ3).
Proof.
  destruct Γ1 as [|Γ1]. intros Γ2 Γ3 [Γ12 V12]; inversion V12.
  induction Γ1 as [|o1 Γ1].
  + intros Γ2 Γ3 V12 V13 V23. rewrite merge_nil_l. assumption. 
  + intros Γ2 Γ3 V12 V13 V23. 
    destruct Γ2 as [|Γ2], Γ3 as [|Γ3]; try solve [inversion V23; inversion H].
    destruct Γ2 as [|o2 Γ2], Γ3 as [|o3 Γ3]; try (rewrite merge_nil_r in *; auto).
    destruct o1, o2, o3; try solve [inversion V12; inversion H];
                         try solve [inversion V13; inversion H];    
                         try solve [inversion V23; inversion H].
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some w :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some w :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some w :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (None :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
Defined.

Lemma valid_split : forall Γ1 Γ2 Γ3, is_valid (Γ1 ⋓ Γ2 ⋓ Γ3) -> 
                                is_valid (Γ1 ⋓ Γ2) /\ is_valid (Γ1 ⋓ Γ3) /\ is_valid (Γ2 ⋓ Γ3).
Proof.
  intros Γ1 Γ2 Γ3 [Γ V].
  unfold is_valid.  
  intuition.
  + destruct (Γ1 ⋓ Γ2); [inversion V | eauto]. 
  + rewrite (merge_comm Γ1 Γ2), <- merge_assoc in V.
    destruct (Γ1 ⋓ Γ3); [rewrite merge_I_r in V; inversion V | eauto]. 
  + rewrite <- merge_assoc in V.
    destruct (Γ2 ⋓ Γ3); [rewrite merge_I_r in V; inversion V | eauto]. 
Defined. 

Ltac valid_invalid_absurd := try (absurd (is_valid Invalid); 
                                  [apply not_valid | auto]; fail).

Lemma size_ctx_merge : forall (Γ1 Γ2 : OCtx), is_valid (Γ1 ⋓ Γ2) ->
                       size_OCtx (Γ1 ⋓ Γ2) = (size_OCtx Γ1 + size_OCtx Γ2)%nat.
Proof.
  intros Γ1 Γ2 valid.
  destruct Γ1 as [ | Γ1];
  destruct Γ2 as [ | Γ2];
    valid_invalid_absurd.
  revert Γ2 valid.
  induction Γ1 as [ | [W1 | ] Γ1]; intros Γ2 valid; 
    [rewrite merge_nil_l; auto | | ];
  (destruct Γ2 as [ | [W2 | ] Γ2]; [rewrite merge_nil_r; auto | |]);
  [ absurd (is_valid Invalid); auto; apply not_valid | | |].
  - specialize IHΓ1 with Γ2.
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H; 
      [absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite IHΓ1; auto. apply valid_valid.
  - specialize IHΓ1 with Γ2.
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H; 
      [absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite IHΓ1; auto. apply valid_valid.
  - specialize IHΓ1 with Γ2.
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H; 
      [absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite IHΓ1; auto. apply valid_valid.
Defined.


(*** Disjointness ***)


Definition Disjoint Γ1 Γ2 : Prop := 
  match Γ1, Γ2 with
  | Invalid, _ => True
  | _, Invalid => True
  | Valid _, Valid _ => is_valid (Γ1 ⋓ Γ2)
  end.
Lemma disjoint_nil_r : forall Γ, Disjoint Γ ∅.
Proof.
  destruct Γ as [ | Γ]; [exact I | ].
  unfold Disjoint. rewrite merge_nil_r. exists Γ. reflexivity.
Defined.


Lemma disjoint_valid : forall Γ1 Γ2, Disjoint Γ1 Γ2 -> is_valid Γ1 -> is_valid Γ2 -> is_valid (Γ1 ⋓ Γ2).
Proof.
  intros Γ1 Γ2 disj [Γ1' valid1] [Γ2' valid2].
  rewrite valid1 in *; rewrite valid2 in *; auto. 
Defined.

Lemma disjoint_merge : forall Γ Γ1 Γ2,
                       Disjoint Γ Γ1 -> Disjoint Γ Γ2 -> Disjoint Γ (Γ1 ⋓ Γ2).
Proof.
  intros Γ Γ1 Γ2 disj1 disj2.
  remember (Γ1 ⋓ Γ2) as Γ'.
  destruct Γ as [ | Γ]; [exact I | ].
  destruct Γ' as [ | Γ']; [exact I | ].
  assert (valid0 : is_valid Γ). { apply valid_valid. }
  assert (valid1 : is_valid Γ1). 
    { destruct Γ1 as [ | Γ1]; [inversion HeqΓ' | ]. apply valid_valid. }
  assert (valid2 : is_valid Γ2).
    { destruct Γ2 as [ | Γ2]; [rewrite merge_I_r in *; inversion HeqΓ' | ]. apply valid_valid. }
  assert (valid1' : is_valid (Γ ⋓ Γ1)). { apply disjoint_valid; auto. }
  assert (valid2' : is_valid (Γ ⋓ Γ2)). { apply disjoint_valid; auto. }
  unfold Disjoint.
  rewrite HeqΓ'.
  rewrite merge_assoc.
  apply valid_join; auto.
  exists Γ'; auto.
Defined.


Lemma disjoint_split : forall Γ1 Γ2 Γ, is_valid Γ1 -> is_valid Γ2 -> 
                                  Disjoint Γ1 Γ2 -> Disjoint (Γ1 ⋓ Γ2) Γ 
                                  -> Disjoint Γ1 Γ /\ Disjoint Γ2 Γ.
Proof.
  intros Γ1 Γ2 Γ [Γ1' valid1] [Γ2' valid2] disj disj'.
  subst. unfold Disjoint in disj.
  destruct Γ as [ | Γ]; [split; exact I | ].
  unfold Disjoint.
  destruct disj as [Γ' is_valid].
  rewrite is_valid in disj'.
  unfold Disjoint in disj'.
  rewrite <- is_valid in disj'.
  apply valid_split in disj'.
  destruct disj' as [H1 [H2 H3]]; split; auto.
Defined.



(*** Automation ***)



(* Local check for multiple evars *)
Ltac has_evars term := 
  match term with
    | ?L = ?R        => has_evar L; has_evar R
    | ?L = ?R        => has_evars L
    | ?L = ?R        => has_evars R
    | ?Γ1 ⋓ ?Γ2      => has_evar Γ1; has_evar Γ2
    | ?Γ1 ⋓ ?Γ2      => has_evars Γ1
    | ?Γ1 ⋓ ?Γ2      => has_evars Γ2
  end.

(* Assumes at most one evar *)
Ltac monoid := 
  try match goal with
  | [ |- ?Γ1 = ?Γ2 ] => has_evar Γ1; symmetry
  end;
  repeat match goal with
  (* reassociate *)
  | [ |- context[?Γ1 ⋓ ?Γ2 ⋓ ?Γ3 ]] => rewrite <- (merge_assoc Γ1 Γ2 Γ3)
  (* solve *)                                            
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  | [ |- ?Γ1 = ?Γ2 ]                => is_evar Γ2; reflexivity
  (* remove nils *)
  | [ |- context[?Γ ⋓ ∅] ]          => rewrite (merge_nil_r Γ)
  | [ |- context[∅ ⋓ ?Γ] ]          => rewrite (merge_nil_l Γ)
  (* move evar to far right *)
  | [ |- _ = ?Γ ⋓ ?Γ' ]             => is_evar Γ; rewrite (merge_comm Γ Γ')
  (* solve nil evars *)
  | [ |- ?Γ = ?Γ ⋓ _ ]              => rewrite merge_nil_r; reflexivity  
  (* cycle and apply merge_cancel_l *)
  | [ |- ?Γ ⋓ _ = ?Γ ⋓ _ ]          => apply merge_cancel_l
  | [ |- ?Γ1 ⋓ ?Γ1' = ?Γ ⋓ _ ]      => rewrite (merge_comm Γ1 Γ1')
(*| [ |- context[?Γ] = ?Γ ⋓ _ ]     => move_left Γ *)
  end.



Lemma test1 : forall x y z, x ⋓ y ⋓ z = z ⋓ x ⋓ y.
Proof. intros. monoid. Qed.

Lemma test2 : forall x, x ⋓ ∅ = x.
Proof. intros. monoid. Qed.

Lemma test21 : forall x, x ⋓ ∅ = x ⋓ ∅.
Proof. intros. monoid. Qed.

Lemma test3 : forall w x y z, x ⋓ (y ⋓ z) ⋓ w = w ⋓ z ⋓ (x ⋓ y).
Proof. intros. monoid. Qed.

Lemma test4 : forall w x y z, x ⋓ (y ⋓ ∅ ⋓ z) ⋓ w = w ⋓ z ⋓ (x ⋓ y).
Proof. intros. monoid. Qed.

Inductive Eqq {A} : A -> A -> Prop := 
| eqq : forall x, Eqq x x.

Lemma create_evar : forall A (x x' y z : A) f, Eqq x x' -> f y x = z -> f y x' = z.
Proof. intros. inversion H; subst. reflexivity. Qed.

Lemma test_evar_ctx : forall x y z, x ⋓ y ⋓ z = z ⋓ x ⋓ y.
Proof. intros. eapply create_evar. 2: monoid. constructor. Qed.


(* Extra helper functions *)
Definition xor_option {a} (o1 : option a) (o2 : option a) : option a :=
  match o1, o2 with
  | Some a1, None => Some a1
  | None, Some a2 => Some a2
  | _   , _       => None
  end.



Fixpoint index (ls : OCtx) (i : nat) : option WType :=
  match ls with
  | Invalid => None
  | Valid [] => None
  | Valid (h :: t) => match i with
              | O => h
              | S i => index (Valid t) i
              end
  end.

(* length is the actual length of the underlying list, as opposed to size, which
 * is the number of Some entries in the list 
 *)
Definition length_OCtx (ls : OCtx) : nat :=
  match ls with
  | Invalid => O
  | Valid ls => length ls
  end.


Lemma merge_dec Γ1 Γ2 : is_valid (Γ1 ⋓ Γ2) + {Γ1 ⋓ Γ2 = Invalid}.
Proof.
  induction Γ1 as [ | Γ1]; [ right; auto | ].
  destruct  Γ2 as [ | Γ2]; [ right; auto | ].
  revert Γ2; induction Γ1 as [ | o1 Γ1]; intros Γ2.
  { simpl. left. apply valid_valid. }
  destruct Γ2 as [ | o2 Γ2]. 
  { simpl. left. apply valid_valid. }
  destruct (IHΓ1 Γ2) as [IH | IH].
  - destruct o1 as [ | W1]; destruct o2 as [ | W2]; simpl in *. 
    { right; auto. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }    
  - right. simpl in *. rewrite IH. destruct (merge_wire o1 o2); auto.
Defined.

(* Patterns and Gates *)

Inductive Pat : Set :=
| unit : Pat
| var : Var -> Pat
| pair : Pat -> Pat -> Pat.

(* Not sure if this is the right approach. See below. *)
Inductive Types_Pat : OCtx -> Pat -> WType -> Set :=
| types_unit : Types_Pat ∅ unit One
| types_var : forall x Γ W, (SingletonCtx x W Γ) -> Types_Pat Γ (var x) W 
| types_pair : forall Γ1 Γ2 Γ p1 p2 w1 w2,
        is_valid Γ 
      -> Γ = Γ1 ⋓ Γ2
      -> Pat Γ1 w1
      -> Pat Γ2 w2
      -> Pat Γ (Tensor w1 w2).

Lemma pat_ctx_valid : forall Γ W, Pat Γ W -> is_valid Γ.
Proof. intros Γ W p. unfold is_valid. inversion p; eauto. Qed.

Open Scope circ_scope.
Inductive Unitary : WType -> Set := 
  | H         : Unitary Qubit 
  | σx        : Unitary Qubit
  | σy        : Unitary Qubit
  | σz        : Unitary Qubit
  | ctrl      : forall {W} (U : Unitary W), Unitary (Qubit ⊗ W) 
  | bit_ctrl  : forall {W} (U : Unitary W), Unitary (Bit ⊗ W) 
  | transpose : forall {W} (U : Unitary W), Unitary W.

(* NOT, CNOT and Tofolli notation *)
Notation NOT := σx.
Notation CNOT := (ctrl σx).
Notation T := (ctrl (ctrl σx)).

Inductive Gate : WType -> WType -> Set := 
  | U : forall {W} (u : Unitary W), Gate W W
  | init0 : Gate One Qubit
  | init1 : Gate One Qubit
  | new0 : Gate One Bit
  | new1 : Gate One Bit
  | meas : Gate Qubit Bit
  | discard : Gate Bit One.

Coercion U : Unitary >-> Gate.
Close Scope circ_scope.
