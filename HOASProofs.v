Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import Arith.
Require Import Omega.
Require Import Psatz.
Require Import List.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Definition I1 := Id (2^0).
Lemma WF_I1 : WF_Matrix 1 1 I1. Proof. unfold I1. apply WF_Id. Qed.
Hint Resolve WF_I1 : wf_db.

Definition HOAS_Equiv {W1 W2} (b1 b2 : Box W1 W2) :=
  forall ρ, Mixed_State ρ -> 〚b1〛 ρ = 〚b2〛 ρ.

Infix "≡" := HOAS_Equiv.

Hint Unfold I1 apply_new0 apply_new1 apply_U apply_meas apply_discard compose_super super swap_list swap_two pad denote_box HOAS_Equiv : den_db.

Lemma Ex : 〚init true〛 I1 = (|1⟩⟨1| : Density 2).
Proof.
  repeat (autounfold with den_db; simpl).
  autorewrite with M_db.
  reflexivity.
Qed.

Require Import FlatCircuits.

Fixpoint pat_map {w} (f : Var -> Var) (p : Pat w) : Pat w :=
  match p with
  | unit => unit
  | qubit x => qubit (f x)
  | bit x => bit (f x)
  | pair p1 p2 => pair (pat_map f p1) (pat_map f p2)
  end.

(* Why are we defining this from scratch??? *)
Fixpoint inb (a : Var) (ls : list Var) : bool :=
  match ls with
  | nil => false
  | b :: ls' => (b =? a) || inb a ls'
  end%bool.

Fixpoint subset (ls1 ls2 : list Var) : bool :=
  match ls1 with
  | nil => true
  | a :: ls1' => inb a ls2 && subset ls1' ls2
  end.
Notation "ls1 ⊆ ls2" := (subset ls1 ls2 = true) (at level 30).

Fixpoint disjoint (ls1 ls2 : list Var) : bool :=
  match ls1 with
  | nil => true
  | a :: ls1' => (negb (inb a ls2)) && disjoint ls1' ls2
  end.
Notation "ls1 ⊥ ls2" := (disjoint ls1 ls2 = true) (at level 30).

Lemma disjoint_nil_l : forall ls, nil ⊥ ls. Proof. reflexivity. Qed.
Lemma disjoint_nil_r : forall ls, ls ⊥ nil. Proof. induction ls; trivial. Qed.

(*
Lemma disjoint_cons : forall a ls1 ls2, (negb (inb a ls1)) = true ->
                                   ls1 ⊥ ls2 ->
                                   ls1 ⊥ (a :: ls2).
Proof.
  intros a ls1 ls2 H H0.
  induction ls1.
  apply disjoint_nil_l.
  simpl in *.
  Search ((_ =? _) = (_ =? _)).
  rewrite Nat.eqb_sym.
  destruct (a0 =? a). simpl in *. inversion H.
  destruct (inb a0 ls2). simpl in *. inversion H0.
  simpl in *.
  apply IHls1; assumption.
Qed.  
*)

Lemma disjoint_cons : forall a ls1 ls2, 
    ((negb (inb a ls1)) && disjoint ls1 ls2 = disjoint ls1 (a :: ls2))%bool.
Proof.
  intros a ls1 ls2.
  induction ls1. reflexivity.
  simpl.
  rewrite <- IHls1.
  rewrite Nat.eqb_sym.
  destruct (a =? a0), (inb a ls1), (inb a0 ls2); auto.
Qed.  

Lemma disjoint_symm : forall ls1 ls2, disjoint ls1 ls2 = disjoint ls2 ls1.
Proof. intros. 
       induction ls1.
       - simpl.
         symmetry.
         apply disjoint_nil_r.
       - simpl.
         rewrite <- disjoint_cons.
         rewrite IHls1.
         reflexivity.
Qed.         
         

Lemma eqb_neq : forall x y, x <> y -> x =? y = false.
Proof.
  induction x as [ | x]; destruct y as [ | y]; intros H; auto.
  - contradiction.
  - simpl.
    apply IHx.
    intros H'.
    subst.
    contradiction.
Qed.

Lemma lookup_app : forall x ls1 ls2,
      lookup x (ls1 ++ ls2) = if inb x ls1 then lookup x ls1 
                                           else (lookup x ls2 + length ls1)%nat.
Proof.
  induction ls1; intros; simpl; auto. 
  destruct (Nat.eq_dec x a) as [H_x_a | H_x_a].
  * subst.
    rewrite Nat.eqb_refl.
    reflexivity.
  * repeat rewrite eqb_neq; auto. simpl.
    rewrite IHls1.
    destruct (inb x ls1); auto.
Qed.

Lemma subset_app : forall ls1 ls2 ls, (ls1 ++ ls2) ⊆ ls -> ls1 ⊆ ls /\ ls2 ⊆ ls.
Proof.
  induction ls1; intros ls2 ls H; simpl in *; split; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    rewrite H_a_ls; simpl.
    apply IHls1 in H.
    destruct H; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    apply IHls1 in H.
    destruct H; auto.
Qed.

Lemma disjoint_app_l : forall ls1 ls2 ls,
      (ls1 ++ ls2) ⊥ ls ->
      ls1 ⊥ ls /\ ls2 ⊥ ls.
Proof.
  induction ls1; intros ls2 ls H; simpl in *; split; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    rewrite H_a_ls; simpl.
    apply IHls1 in H.
    destruct H; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    apply IHls1 in H.
    destruct H; auto.
Qed.

Lemma disjoint_app_r : forall ls1 ls2 ls,
      ls1 ⊥ ls -> 
      ls2 ⊥ ls ->
      (ls1 ++ ls2) ⊥ ls.
Proof.
  induction ls1; intros ls2 ls H H0.
  - simpl. assumption.
  - simpl in *.
    apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    rewrite H_a_ls.
    simpl.
    apply IHls1; assumption.
Qed.

Lemma hash_pat_app_l : forall {w} (p : Pat w) ls1 ls2, 
      (* dom p ∩ ls1 = dom p *)
      pat_to_list p ⊆ ls1 ->
      hash_pat p (ls1 ++ ls2) = hash_pat p ls1.
Proof.
  induction p; intros ls1 ls2 H_intersect; simpl in *; auto.
    + rewrite lookup_app.
      rewrite Bool.andb_true_r in H_intersect.
      rewrite H_intersect.
      reflexivity.
    + rewrite lookup_app.
      rewrite Bool.andb_true_r in H_intersect.
      rewrite H_intersect.
      reflexivity.
    + apply subset_app in H_intersect.
      destruct H_intersect as [H_intersect1 H_intersect2].
      rewrite IHp1; auto. rewrite IHp2; auto.
Qed.

Lemma hash_pat_app_r :  forall {w} (p : Pat w) ls1 ls2,
      (* dom p ∩ ls1 = ∅ *)
      (pat_to_list p) ⊥ ls1 ->
      hash_pat p (ls1 ++ ls2)
    = pat_map (fun x => x + length ls1)%nat (hash_pat p ls2).
Proof.
  induction p; intros ls1 ls2 H_intersect; simpl in *; auto.
  - rewrite lookup_app. 
    rewrite Bool.andb_true_r in H_intersect.
    apply Bool.negb_true_iff in H_intersect.
    rewrite H_intersect. reflexivity.
  - rewrite lookup_app. 
    rewrite Bool.andb_true_r in H_intersect.
    apply Bool.negb_true_iff in H_intersect.
    rewrite H_intersect. reflexivity.
  - apply disjoint_app_l in H_intersect.
    destruct H_intersect as [H_intersect1 H_intersect2].
    rewrite IHp1; auto.
    rewrite IHp2; auto.
Qed.

Lemma pat_to_list_pat_map : forall {w} (p : Pat w) f, 
      pat_to_list (pat_map f p) = map f (pat_to_list p).
Proof.  
  induction p; intros; auto.
  simpl. rewrite IHp1, IHp2. 
  rewrite map_app.
  reflexivity.
Qed.
Lemma pat_size_length_list : forall {w} (p : Pat w), 
      pat_size p = length (pat_to_list p).
Proof.
  induction p; auto.
  unfold pat_size in *. simpl. rewrite IHp1, IHp2.
  rewrite app_length.
  reflexivity.
Qed.


Lemma map_seq : forall len offset start,
      map (fun x => x + offset)%nat (seq start len) = seq (start + offset) len.
Proof.
  induction len; intros; simpl; auto.
  rewrite IHlen.
  reflexivity.
Qed.


Lemma seq_app : forall offset1 offset2 start,
      seq start offset1 ++ seq (start + offset1) offset2 
    = seq start (offset1 + offset2).
Proof.
  induction offset1; intros; simpl; auto.
  rewrite Nat.add_succ_r.
  rewrite <- Nat.add_succ_l.
  rewrite IHoffset1.
  reflexivity.
Qed.

Inductive WF_Pat : forall {w}, Pat w -> Prop :=
| WF_unit : WF_Pat unit
| WF_qubit : forall x, WF_Pat (qubit x)
| WF_bit : forall x, WF_Pat (bit x)
| WF_pair : forall w1 w2 (p1 : Pat w1) (p2 : Pat w2), 
            pat_to_list p2 ⊥ pat_to_list p1 -> 
            WF_Pat p1 -> WF_Pat p2 -> WF_Pat (pair p1 p2)
.

Lemma subset_cons_r : forall ls1 ls2 a, ls1 ⊆ ls2 -> ls1 ⊆ (a :: ls2).
Proof.
  induction ls1 as [ | b ls1]; intros; simpl in *; auto.
    apply Bool.andb_true_iff in H.
    destruct H as [H_b_ls2 H].
    rewrite H_b_ls2.
    rewrite IHls1; auto.
    rewrite Bool.orb_true_r; auto.
Qed.

Lemma subset_refl : forall ls, ls ⊆ ls.
Proof.
  induction ls; simpl; auto.
  rewrite Nat.eqb_refl. simpl.
  apply subset_cons_r; auto.
Qed.
  

Lemma hash_pat_pat_to_list : forall {w} (p : Pat w), 
    WF_Pat p ->
    pat_to_list (hash_pat p (pat_to_list p)) = seq 0 (pat_size p).
Proof.
  intros w p wf_p.
  induction wf_p; simpl; try rewrite Nat.eqb_refl; auto.
  rewrite hash_pat_app_l; [ | apply subset_refl].
  rewrite IHwf_p1.
  rewrite hash_pat_app_r; auto.
  rewrite pat_to_list_pat_map.
  rewrite IHwf_p2.
  rewrite <- pat_size_length_list.
  rewrite map_seq.
  simpl.
  rewrite seq_app.
  reflexivity.
Qed.

(*
Lemma fresh_pat_size : forall W p m,
      fresh_pat W m = p ->
      pat_size p = 〚W〛.
Proof.
  reflexivity.
Qed.

Lemma fresh_pat_increasing : forall W n n' p,
  fresh_pat W n = (p, n') ->
  (n <= n')%nat.
Proof.
  intros W.
  induction W; intros n n' p H.
  + inversion H. omega.
  + inversion H. omega.
  + inversion H. omega.
  + inversion H. 
    destruct (fresh_pat W1 n) as [p1 m] eqn:E. 
    destruct (fresh_pat W2 m) as [p2 m'] eqn:E'.
    inversion H1; subst.
    apply IHW2 in E'.
    apply IHW1 in E.
    omega.
Qed.  

Lemma pat_to_list_empty : forall W n p,
    fresh_pat W n = (p,0) ->
    pat_to_list p = nil.
Proof.
  intros W.
  induction W; intros n p H; inversion H; subst.
  reflexivity.
  destruct (fresh_pat W1 n) as [p1 n'] eqn:E.
  destruct (fresh_pat W2 n') as [p2 n''] eqn:E'.
  inversion H1; subst.
  simpl.
  replace n' with O in * by (specialize (fresh_pat_increasing _ _ _ _ E'); omega).
  replace n with O in * by (specialize (fresh_pat_increasing _ _ _ _ E); omega).
  rewrite (IHW2 _ _ E').
  rewrite (IHW1 _ _ E).
  reflexivity.
Qed.  
*)

Lemma n_nm_neq : forall n m, n =? n + 1 + m = false.
Proof. intros. induction n. simpl. reflexivity.
       simpl. assumption.
Qed.

Lemma fresh_pat_disjoint_aux : forall W1 W2 n m p1 p2,
      p1 = fresh_pat W1 n ->
      p2 = fresh_pat W2 (n + size_WType W1 + m ) ->
      pat_to_list p2 ⊥ pat_to_list p1.
Proof.
  induction W1; intros.
  - simpl in *. subst. 
    generalize dependent m.
    induction W2; intros. 
    + simpl. rewrite n_nm_neq. reflexivity. 
    + simpl. rewrite n_nm_neq. reflexivity. 
    + simpl. reflexivity.
    + simpl. apply disjoint_app_r. apply IHW2_1. rewrite <- plus_assoc. apply IHW2_2.
  - simpl in *. subst. 
    generalize dependent m.
    induction W2; intros. 
    + simpl. rewrite n_nm_neq. reflexivity. 
    + simpl. rewrite n_nm_neq. reflexivity. 
    + simpl. reflexivity.
    + simpl. apply disjoint_app_r. apply IHW2_1. rewrite <- plus_assoc. apply IHW2_2.
  - simpl in H. subst. simpl. apply disjoint_nil_r.
  - subst.
    simpl.
    rewrite disjoint_symm.
    apply disjoint_app_r; rewrite disjoint_symm.
    eapply IHW1_1.
    reflexivity.
    rewrite plus_assoc.
    rewrite <- plus_assoc.
    reflexivity.
    eapply IHW1_2.
    reflexivity.
    rewrite plus_assoc.
    reflexivity.
Qed.

Lemma fresh_pat_disjoint : forall W1 W2 n p1 p2,
      p1 = fresh_pat W1 n ->
      p2 = fresh_pat W2 (n + size_WType W1) ->
      pat_to_list p2 ⊥ pat_to_list p1.
Proof. intros. apply fresh_pat_disjoint_aux with (n:=n) (m:=O). 
       apply H. rewrite plus_0_r. apply H0.
Qed.    

Lemma fresh_pat_wf : forall W p m, fresh_pat W m = p -> WF_Pat p.
Proof.
  induction W; simpl; intros.
  - inversion H. constructor.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H.
    constructor; auto; [ | eapply IHW1; eauto | eapply IHW2; eauto].
    eapply fresh_pat_disjoint; eauto.
Qed.

Lemma pat_WType_size : forall W (p : Pat W), pat_size p = size_WType W.
Proof. reflexivity. Qed.

Lemma id_circ_Id : forall W ρ, WF_Matrix (2^〚W〛) (2^〚W〛) ρ -> 
    〚@id_circ W〛 ρ = ρ.
Proof.
  intros W ρ H. 
  repeat (simpl; autounfold with den_db).
  remember (FlatCircuits.fresh_pat W 0) as p.
  assert (wf_p : WF_Pat p) by (apply (fresh_pat_wf W p 0); auto).
  repeat (simpl; autounfold with den_db).
  rewrite hash_pat_pat_to_list; auto.
(*  rewrite pat_size_hash_pat.*)
  replace (swap_list_aux _ _ (zip_to 0 (size_WType W) (seq 0 (pat_size p)))) 
    with (swap_list (size_WType W) (seq 0 (pat_size p))) 
    by reflexivity. 
  rewrite pat_WType_size.
  rewrite swap_list_n_id.
  autorewrite with M_db.
  reflexivity.
Qed.
 
Lemma unitary_transpose_id_qubit : forall (U : Unitary Qubit), forall ρ,
   WF_Matrix (2^〚Qubit〛) (2^〚Qubit〛) ρ -> 
   〚unitary_transpose U〛 ρ = 〚@id_circ Qubit〛 ρ.
Proof.
  intros U ρ pf_ρ.
  assert (unitary_U : is_unitary (denote_unitary U)) by apply unitary_gate_unitary.
  destruct unitary_U as [WF inv].
  repeat (autounfold with den_db; simpl in *).
  autorewrite with M_db.
  repeat rewrite Mmult_assoc; try rewrite inv.
  repeat rewrite <- Mmult_assoc; try rewrite inv.
  autorewrite with M_db.
  reflexivity.
Qed.

Lemma unitary_transpose_id : forall W (U : Unitary W) (ρ : Density (2^〚W〛 )),
  WF_Matrix (2^〚W〛) (2^〚W〛) ρ ->
  〚unitary_transpose U〛 ρ = 〚@id_circ W〛 ρ.
Proof.
  intros W U ρ wfρ. 
  specialize (unitary_gate_unitary U); intros [WFU UU].
  repeat (simpl; autounfold with den_db).
  remember (FlatCircuits.fresh_pat W 0) as p.
  assert (wf_p : WF_Pat p) by (apply (fresh_pat_wf W p 0); auto).
  repeat (simpl; autounfold with den_db).

  rewrite minus_plus, Nat.leb_refl.
  rewrite Nat.sub_diag.

  rewrite hash_pat_pat_to_list; auto.
  rewrite pat_WType_size.
  setoid_rewrite (swap_list_n_id (size_WType W)).
  autorewrite with M_db.

  repeat rewrite Mmult_assoc.
  setoid_rewrite UU.
  repeat rewrite <- Mmult_assoc.
  setoid_rewrite UU.
  autorewrite with M_db.
  reflexivity.
Qed.

Definition fair_coin : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => 1/2
          | 1, 1 => 1/2
          | _, _ => 0
          end.

Definition biased_coin (c : C) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => (1 - c) 
          | 1, 1 => c
          | _, _ => 0
          end.

Lemma bias1 : biased_coin 1 = |1⟩⟨1|.
Proof.
  unfold biased_coin.
  prep_matrix_equality; simpl.
  destruct_m_eq; clra.
Qed.

Lemma even_bias : biased_coin (1/2) = fair_coin.
Proof. 
  unfold biased_coin, fair_coin.
  prep_matrix_equality; simpl.
  destruct_m_eq; clra.
Qed.

Lemma fair_toss : 〚coin_flip〛 I1  = fair_coin.
Proof.
  repeat (autounfold with den_db; simpl).
  autorewrite with M_db.
  prep_matrix_equality.
  autounfold with M_db.
  simpl; autorewrite with C_db.
  destruct x, y; simpl; autorewrite with C_db; destruct_m_eq; clra.
Qed.

Fixpoint upper_bound (li : list nat) : nat :=
  match li with
  | nil => 0
  | n :: li' => max (S n) (upper_bound li')
  end.

Definition denote_circuit {w1 w2} (p : Pat w1) (c : Circuit w2) 
                        : Superoperator (2^〚w1〛) (2^〚w2〛) :=
  let li := pat_to_list p in
  let n := upper_bound li in
  denote_min_circuit (〚w1〛) (hoas_to_min c li (S n)).


(* Do these belong back in Denotation? *) 
Lemma compose_correct : forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2),
      Typed_Box g -> Typed_Box f ->
      〚inSeq f g〛 = compose_super (〚g〛) (〚f〛).
Proof.
  intros.
  autounfold with den_db; simpl. 
  destruct f as [f], g as [g]. 
  autounfold with den_db; simpl. 
  remember (fresh_pat W1 0) as p eqn:H_p_n.
  autounfold with den_db; simpl. 
  set (c := f p).
  induction c eqn:E.
  - autounfold with den_db; simpl. 
    unfold denote_min_box.
    simpl.
    apply FunctionalExtensionality.functional_extensionality.
    intros ρ.
    simpl.
    remember (fresh_pat W2 0) as p2' eqn:H_p_n2.
    assert (size_WType W1 = size_WType W2).
      unfold Typed_Box in H0.
      simpl in H0.
      admit.
Abort.


Lemma flips_correct : forall n, 〚coin_flips n〛 I1 = biased_coin (2^n).
Proof.
  induction n.  
  + repeat (autounfold with den_db; simpl).    
    autorewrite with M_db.
    prep_matrix_equality.
    autounfold with M_db.
    destruct_m_eq; clra.
  + simpl.
    repeat (simpl; autounfold with den_db). 
Abort.

Lemma cnot_eq : cnot = control σx.
Proof.
  autounfold with M_db.
  simpl.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; autorewrite with C_db; trivial).
Qed.

(*
Opaque Nat.div.
Opaque Nat.modulo.
*)

Lemma divmod_eq : forall x y n z, fst (Nat.divmod x y n z) = (n + fst (Nat.divmod x y 0 z))%nat.
Proof.
  induction x.
  + intros. simpl. omega.
  + intros. simpl. 
    destruct z.
    rewrite IHx.
    rewrite IHx with (n:=1%nat).
    omega.
    rewrite IHx.
    reflexivity.
Qed.

(** Tactics for solving computational matrix equalities **)
(* Construct matrices full of evars *)
Ltac mk_evar t T := match goal with _ => evar (t : T) end.

Ltac evar_list n := 
  match n with 
  | O => constr:(@nil C)
  | S ?n' => let e := fresh "e" in
            let none := mk_evar e C in 
            let ls := evar_list n' in 
            constr:(e :: ls)
            
  end.

Ltac evar_list_2d m n := 
  match m with 
  | O => constr:(@nil (list C))
  | S ?m' => let ls := evar_list n in 
            let ls2d := evar_list_2d m' n in  
            constr:(ls :: ls2d)
  end.

Ltac evar_matrix m n := let ls2d := (evar_list_2d m n) 
                        in constr:(list2D_to_matrix ls2d).   

(* Tactic version of Nat.lt *)
Ltac tac_lt m n := 
  match n with 
  | S ?n' => match m with 
            | O => idtac
            | S ?m' => tac_lt m' n'
            end
  end.

(* Reassociate matrices so that smallest dimensions are multiplied first:
 m n o    p
(A × B) × C => A × (B × C) iff
  1) p < o && p < m
  2) n < o && n < m

m n    o p
A × (B × C) => (A × B) × C iff
  1) m < n && m < p
  2) o < n && o < p
*)
Ltac assoc_least := 
  repeat (simpl; match goal with
  | [|- context[@Mmult ?m ?o ?p (@Mmult ?m ?n ?o ?A ?B) ?C]] => tac_lt p o; tac_lt p m; 
       setoid_rewrite (Mmult_assoc _ _ _ _ A B C)
  | [|- context[@Mmult ?m ?o ?p (@Mmult ?m ?n ?o ?A ?B) ?C]] => tac_lt n o; tac_lt n m; 
       setoid_rewrite (Mmult_assoc _ _ _ _ A B C)
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt m n; tac_lt m p; 
       setoid_rewrite <- (Mmult_assoc _ _ _ _ A B C)
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt o n; tac_lt o p; 
       setoid_rewrite <- (Mmult_assoc _ _ _ _ A B C)
  end).

(* Helper function for crunch_matrix *)
Ltac solve_out_of_bounds := 
  repeat match goal with 
  | [H : WF_Matrix _ _ ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (left; simpl; omega) 
  | [H : WF_Matrix _ _ ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (right; simpl; omega) 
  end;
  autorewrite with C_db; auto.

(* Unify A × B with list (list (evars)) *)
(* We convert the matrices back to functional representation for 
   unification. Simply comparing the matrices may be more efficient,
   however. *)
Ltac crunch_matrix := match goal with 
                      | [|- ?G ] => idtac "Crunching:" G
                      end;
                      repeat match goal with
                             | [ H : C |- _ ] => unfold H; clear H
                             end; 
                      simpl;
                      unfold list2D_to_matrix;    
                      autounfold with M_db;
                      prep_matrix_equality;
                      simpl;
                      destruct_m_eq;
                      try rewrite divmod_eq; 
                      simpl;
                      autorewrite with C_db; 
                      try reflexivity;
                      try solve_out_of_bounds. 

Ltac compound M := 
  match M with
  | ?A × ?B  => idtac
  | ?A .+ ?B => idtac 
  | ?A †     => compound A
  end.

(* Reduce inner matrices first *)
Ltac reduce_aux M := 
  match M with 
  | ?A .+ ?B     => compound A; reduce_aux A
  | ?A .+ ?B     => compound B; reduce_aux B
  | ?A × ?B      => compound A; reduce_aux A
  | ?A × ?B      => compound B; reduce_aux B
  |  @Mmult ?m ?n ?o ?A ?B        => let M' := evar_matrix m o in
                                    replace M with M';
                                    [| crunch_matrix ] 
  | @Mplus ?m ?n ?A ?B            => let M' := evar_matrix m n in
                                    replace M with M';
                                    [| crunch_matrix ] 
  end.

Ltac reduce_matrix := match goal with 
                       | [ |- ?M = _] => reduce_aux M
                       | [ |- _ = ?M] => reduce_aux M
                       end;
                       repeat match goal with | [ H : C |- _ ] => unfold H; clear H end.

Ltac solve_matrix := assoc_least; repeat reduce_matrix; crunch_matrix.

(** /computational matrix tactics **)

Lemma swap_swap : swap × swap = Id 4.
Proof.
  solve_matrix.
  destruct (x =? y); auto.
Qed.

Lemma swap_swap_r : forall n A, WF_Matrix n 4 A ->
      A × swap × swap = A.
Proof.
  intros.
  rewrite Mmult_assoc.
  rewrite swap_swap. 
  apply Mmult_1_r.
  auto.
Qed.

Hint Rewrite swap_swap swap_swap_r using (auto 100 with wf_db): M_db.

Definition EPR00 : Matrix 4 4 :=
  fun x y => match x, y with
             | 0, 0 => 1/2
             | 0, 3 => 1/2
             | 3, 0 => 1/2
             | 3, 3 => 1/2
             | _, _ => 0
             end.

Lemma bell00_eq :  〚bell00〛 I1  = EPR00.
Proof.
  repeat (simpl; autounfold with den_db). 
  autorewrite with M_db. 
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db.
  solve_matrix.
Qed.

(* Deutsch's Algorithm *)

Delimit Scope circ_scope with qc.

Ltac find_smallest M := 
  match M with 
  | ?A × ?B         => find_smallest A
  | ?A .+ ?B        => find_smallest A
  (* fall through cases - only returns sums/products *)
  | ?A × ?B         => M
  | ?A .+ ?B        => M
  end.                    

(* f(x) = 0. Unitary: Identity *)
Definition f0 : Matrix 4 4 := Id 4.

(* f(x) = x. Unitary: CNOT *)
Definition f1 : Matrix 4 4 := control σx.

(* f(x) = 1 - x. Unitary: inverse CNOT *)
Definition f2 : Matrix 4 4 := fun x y =>
  match x, y with
  | 0, 1 | 1, 0 | 2, 2 | 3, 3 => 1
  | _, _                      => 0
  end.

(* f(x) = 1. Unitary: Id ⊗ X *)
Definition f3 : Matrix 4 4 := Id 2 ⊗ σx.

Definition constant (U : Unitary (Qubit ⊗ Qubit)%qc) := 
                       denote_unitary U = f0 \/ denote_unitary U = f3.
Definition balanced (U : Unitary (Qubit ⊗ Qubit)%qc) := 
                       denote_unitary U = f1 \/ denote_unitary U = f2.

Lemma f2_WF : WF_Matrix 4 4 f2. Proof. show_wf. Qed.
Hint Resolve f2_WF : wf_db.

Ltac c_ineq := apply C0_fst; specialize Rlt_sqrt2_0; intros; simpl; Psatz.lra.

(* Maybe create new database for solving sqrt2 equalities? *)
Hint Rewrite Cplus_opp_l Cplus_opp_r Copp_involutive Copp_0 : C_db. 
Hint Rewrite Csqrt_sqrt using Psatz.lra : C_db.
Hint Rewrite <- Copp_mult_distr_l Copp_mult_distr_r Cdouble : C_db. 
Hint Rewrite <- Cinv_mult_distr using c_ineq : C_db.
Hint Rewrite Cinv_l Cinv_r using c_ineq : C_db.
  
(* Temporarily commented out for efficient compilation *)
Lemma deutsch_constant : forall U_f, constant U_f -> 
                                〚deutsch U_f〛 I1 = |0⟩⟨0|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  autorewrite with M_db.
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 

  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  autorewrite with M_db. 
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_r.
  autorewrite with M_db. 
  destruct H; rewrite H; clear.
  + (* f0 *)
    unfold f0.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
  + (* f3 *)
    unfold f3.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
Qed.

Lemma deutsch_balanced : forall U_f, balanced U_f -> 
                                〚deutsch U_f〛 I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  autorewrite with M_db.
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 

  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  autorewrite with M_db. 
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_r.
  autorewrite with M_db. 
  
  destruct H; rewrite H; clear.
  + (* f1 *)
    unfold f1.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
  + (* f2 *)
    unfold f2.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
Qed.

(* Let's see if not distributing is faster *)
Lemma deutsch_balanced' : forall U_f, balanced U_f -> 
                                〚deutsch U_f〛 I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  autorewrite with M_db.
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 
  destruct H; rewrite H; clear.
  + (* f1 *)
    unfold f1.
    solve_matrix.
    rewrite (Cmult_comm (1/√2) (1/2)).
    repeat rewrite <- Cmult_assoc.
    rewrite (Cmult_comm (1/√2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite Cmult_assoc.
    rewrite <- (Cmult_assoc 2 2 _).
    autorewrite with C_db.
    reflexivity.
  + (* f2 *)
    unfold f2.
    solve_matrix.
    rewrite (Cmult_comm (1/√2) (1/2)).
    repeat rewrite <- Cmult_assoc.
    rewrite (Cmult_comm (1/√2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite Cmult_assoc.
    rewrite <- (Cmult_assoc 2 2 _).
    autorewrite with C_db.
    reflexivity.
Qed.

(* We convert the matrices back to functional representation for 
   unification. Simply comparing the matrices may be more efficient,
   however. *)

(*
Lemma teleport_eq : forall (ρ : Density 2), 
  Mixed_State ρ -> denote_box teleport ρ = ρ.
Proof.
  intros ρ H.
  idtac.
  repeat (simpl; autounfold with den_db). 
  autorewrite with M_db.
  repeat (setoid_rewrite kron_conj_transpose).
  autorewrite with M_db.
  idtac.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  
  (* This makes progress. Haven't managed to run to completion yet. *)
  repeat reduce_matrix.
  solve_matrix.
  

Abort.
*)

(* Lemmas out of date
Lemma boxed_gate_correct : forall W1 W2 (g : Gate W1 W2) (ρ : Density (2^〚W1〛)) ,
      Mixed_State (2^〚W1〛) (2^〚W1〛) ρ -> 〚boxed_gate g〛 ρ = 〚g〛 ρ.
Proof.
  intros W1 W2 g ρ wf_ρ. simpl.
  unfold denote_pat_in.
  repeat rewrite merge_nil_r.
  repeat rewrite size_fresh_ctx.
  repeat rewrite fresh_pat_empty.
  repeat rewrite map_num_wires_before.
  repeat rewrite swap_list_n_id.
  unfold super, compose_super.
  repeat rewrite mult_1_r.
  assert (wf_g : WF_Matrix (2^〚W2〛) (2^〚W2〛) (〚g〛 ρ)).
    generalize (WF_denote_gate 0 _ _ g ρ); intros.
    simpl in *. repeat rewrite mult_1_r in *. unfold denote_gate. apply (H wf_ρ).
  autorewrite with M_db.
  reflexivity.
Qed.

Lemma lift_meas_correct : lift_meas ≡ boxed_gate meas.
Proof.
  intros ρ wf_ρ.
  simpl.
  repeat (unfold denote_pat_in, swap_list, swap_two; simpl).
  Msimpl.
  unfold super, compose_super, Splus, SZero.
  Msimpl.
  rewrite braket0_conj_transpose, braket1_conj_transpose.
  prep_matrix_equality; simpl.
  unfold Mplus, Mmult, Id, conj_transpose, Zero. simpl.
  autorewrite with C_db.
  rewrite Cplus_comm. reflexivity.
Qed.

Lemma lift_eta_correct : forall (ρ : Density 2), WF_Matrix 2 2 ρ
      -> 〚lift_eta Bit〛 ρ = 〚@id_circ Bit〛 ρ.
Abort (* This is only true if ρ is a classical state *).
(* Proof.
  intros ρ wf_ρ.
  simpl.
  repeat (unfold denote_pat_in, swap_list, swap_two; simpl).
  Msimpl.
  unfold super, compose_super, Splus, SZero. 
  Msimpl.
  prep_matrix_equality.
  unfold Mmult, Mplus, Zero, conj_transpose, ket0, ket1. simpl.
  Csimpl.
  destruct x; Csimpl. 
  destruct y; Csimpl.
*)
*)


