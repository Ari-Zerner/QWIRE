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

Hint Unfold I1 apply_new0 apply_new1 apply_U apply_meas apply_discard compose_super super swap_list swap_two pad denote_box : den_db.

Lemma Ex : denote_box One (init true) I1 = (|1⟩⟨1| : Density 2).
Proof.
  repeat (autounfold with den_db; simpl).
  autorewrite with M_db.
  reflexivity.
Qed.

Definition HOAS_Equiv (b1 b2 : Box) :=
  forall W ρ, WF_Matrix (2^〚W〛) (2^〚W〛) ρ -> 
         denote_box W b1 ρ = denote_box W b2 ρ.

Lemma unitary_transpose_id_qubit : forall (U : Unitary Qubit), forall ρ,
   WF_Matrix (2^〚Qubit〛) (2^〚Qubit〛) ρ -> 
   denote_box Qubit (unitary_transpose U) ρ = denote_box Qubit id_circ ρ.
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

(* I don't know how to reason parametrically about these denotations... *)
Lemma unitary_transpose_id : forall W (U : Unitary W) (ρ : Density (2^〚W〛 )),
  WF_Matrix (2^〚W〛) (2^〚W〛) ρ ->
  denote_box W (unitary_transpose U) ρ = denote_box W id_circ ρ.
Proof.
  intros W U ρ pf_ρ.  
  induction W.
  + repeat (autounfold with den_db; simpl).
    specialize (unitary_gate_unitary U). unfold is_unitary. simpl. 
    intros [WFU UU].
    autorewrite with M_db.
    repeat rewrite Mmult_assoc.
    rewrite UU.
    repeat rewrite <- Mmult_assoc.
    rewrite UU.
    autorewrite with M_db.
    reflexivity.
  + repeat (autounfold with den_db; simpl).
    specialize (unitary_gate_unitary U). unfold is_unitary. simpl. 
    intros [WFU UU].
    autorewrite with M_db.
    repeat rewrite Mmult_assoc.
    rewrite UU.
    repeat rewrite <- Mmult_assoc.
    rewrite UU.
    autorewrite with M_db.
    reflexivity.
  + repeat (autounfold with den_db; simpl).
    specialize (unitary_gate_unitary U). unfold is_unitary. simpl. 
    intros [WFU UU].
    autorewrite with M_db.
    repeat rewrite Mmult_assoc.
    rewrite UU.
    repeat rewrite <- Mmult_assoc.
    rewrite UU.
    autorewrite with M_db.
    reflexivity.
  + repeat (autounfold with den_db; simpl).
    simpl.
Abort.

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

Lemma fair_toss : denote_box One coin_flip I1  = fair_coin.
Proof.
  repeat (autounfold with den_db; simpl).
  autorewrite with M_db.
  prep_matrix_equality.
  autounfold with M_db.
  simpl; autorewrite with C_db.
  destruct x, y; simpl; autorewrite with C_db; destruct_m_eq; clra.
Qed.

Lemma flips_correct : forall n, denote_box One (coin_flips n) I1 = biased_coin (2^n).
Proof.
  induction n.  
  + repeat (autounfold with den_db; simpl).    
    autorewrite with M_db.
    prep_matrix_equality.
    autounfold with M_db.
    destruct_m_eq; clra.
  + simpl. 
Abort.

Lemma cnot_eq : cnot = control pauli_x.
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

(* Unify A × B with list (list (evars)) *)
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
                      autorewrite with C_db; try reflexivity.

Ltac reduce_aux M := 
  match M with 
  | ?A × ?B     => reduce_aux A  (* will fail if A is not a product/sum *)
  | ?A .+ ?B    => reduce_aux A  (* will fail if A is not a product/sum *)
  | ?A .+ ?B    => reduce_aux B  (* for addition, reduce both sides first *)
  |  @Mmult ?m ?n ?o ?A ?B        => let M' := evar_matrix m o in
                                    replace M with M';
                                    [| crunch_matrix ] 
  | @Mplus ?m ?n ?A ?B            => let M' := evar_matrix m n in
                                    replace M with M';
                                    [| crunch_matrix ] 
  end.

(* Replace smallest A × B with their product *)
Ltac reduce_matrix := match goal with [ |- ?M = _] => reduce_aux M end;
                      repeat match goal with | [ H : C |- _ ] => unfold H; clear H end.

Ltac solve_matrix := repeat reduce_matrix; crunch_matrix.


(* Faster version, puts goal has the form (... × |φ⟩) × (⟨φ| × ...) *)
(* Rewrite to focus on specific parts, use has_bra and has_ket subroutines. *)
Ltac assoc_center := 
  (* associate left *)
  repeat rewrite <- Mmult_assoc; 
  repeat progress match goal with
                  (* termination  *)
                  | [|- _ × (⟨0| × _) = _]        => idtac
                  | [|- _ × (⟨1| × _) = _]        => idtac
                  | [|- _ × ((⟨0| ⊗ _) × _) = _]  => idtac
                  | [|- _ × ((⟨1| ⊗ _) × _) = _]  => idtac
                  (* associate right *)
                  | _                       => rewrite Mmult_assoc
                  end.

Ltac reduce_aux_l M := 
  match M with 
  | ?A × ?B     => reduce_aux A  (* will fail if A is not a product/sum *)
  | ?A .+ ?B    => reduce_aux A  (* will fail if A is not a product/sum *)
  |  @Mmult ?m ?n ?o ?A ?B        => let M' := evar_matrix m o in
                                    replace M with M';
                                    [| crunch_matrix ] 
  | @Mplus ?m ?n ?A ?B            => let M' := evar_matrix m n in
                                    replace M with M';
                                    [| crunch_matrix ] 
  end.

Ltac reduce_aux_r M := 
  match M with 
  | ?A × ?B     => reduce_aux B  (* will fail if A is not a product/sum *)
  | ?A .+ ?B    => reduce_aux B  (* will fail if A is not a product/sum *)
  |  @Mmult ?m ?n ?o ?A ?B        => let M' := evar_matrix m o in
                                    replace M with M';
                                    [| crunch_matrix ] 
  | @Mplus ?m ?n ?A ?B            => let M' := evar_matrix m n in
                                    replace M with M';
                                    [| crunch_matrix ] 
  end.

Ltac reduce_matrix_c := match goal with [ |- ?L × ?R = _] => 
                                       reduce_aux_r L;
                                       reduce_aux_l R
                       end;
                       repeat match goal with | [ H : C |- _ ] => unfold H; clear H end.

Ltac solve_matrix_c := repeat reduce_matrix_c; crunch_matrix.

(** /computational matrix tactics **)


Definition EPR00 : Matrix 4 4 :=
  fun x y => match x, y with
             | 0, 0 => 1/2
             | 0, 3 => 1/2
             | 3, 0 => 1/2
             | 3, 3 => 1/2
             | _, _ => 0
             end.

Lemma bell00_eq :  denote_box One bell00 I1  = EPR00.
Proof.
  repeat (simpl; autounfold with den_db). 
  autorewrite with M_db. 
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 
  assoc_center.
  solve_matrix_c.
Qed.

(* Deutsch's Algorithm *)

Ltac find_smallest M := 
  match M with 
  | ?A × ?B         => find_smallest A
  | ?A .+ ?B        => find_smallest A
  (* fall through cases - only returns sums/products *)
  | ?A × ?B         => M
  | ?A .+ ?B        => M
  end.                    


Definition f2 : Matrix 4 4 := fun x y =>
  match x, y with
  | 0, 1 | 1, 0 | 2, 2 | 3, 3 => 1
  | _, _                      => 0
  end.

Lemma f2_WF : WF_Matrix 4 4 f2. Proof. show_wf. Qed.
Hint Resolve f2_WF : wf_db.

Lemma deutsch2 : forall U_f, 
    denote_unitary U_f = f2 -> 
    denote_box One (deutsch U_f) I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  rewrite H. clear H.
  autorewrite with M_db. 
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.

  repeat reduce_matrix.
  crunch_matrix.

  clra.
  all: try clra.
  all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).

  Ltac c_ineq := apply C0_fst; specialize Rlt_sqrt2_0; intros; simpl; Psatz.lra.
  
  Hint Rewrite Cplus_opp_l Copp_involutive : C_db. 
  Hint Rewrite Csqrt_sqrt using Psatz.lra : C_db.
  Hint Rewrite <- Copp_mult_distr_l Copp_mult_distr_r Cdouble : C_db. 
  Hint Rewrite <- Cinv_mult_distr using c_ineq : C_db.
  Hint Rewrite Cinv_r using c_ineq : C_db.


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

(* These don't work yet... *)
Ltac num_terms T := 
  match T with 
  | ?f ?a ?b => num_terms a + num_terms b
  | _        => 1
  end.

Ltac proof_size := 
  match goal with 
  | [|- ?A = ?B] => num_terms A + num_terms B
  end.


Lemma teleport_eq : forall (ρ : Density 2), 
  WF_Matrix 2 2 ρ -> denote_box Qubit teleport ρ = ρ.
Proof.
  intros ρ H.
  idtac.
  repeat (simpl; autounfold with den_db). 
  autorewrite with M_db.
  repeat (setoid_rewrite kron_conj_transpose).
  autorewrite with M_db.
  
  
  repeat rewrite <- Mmult_assoc. 


  
  let n := proof_size in idtac n.



  reduce_matrix.

  


  rewrite Mmult_plus_distr_l.
  



  Set Printing Depth 100.
  reduce_matrix.
  
  Search ".+".
  reduce_matrix.
  solve_matrix.
Abort.

(* Do these belong back in Denotation? *)
Program Lemma compose_correct : forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2),
      〚inSeq f g〛 = compose_super (〚g〛) (〚f〛).
Admitted.

Lemma boxed_gate_correct : forall W1 W2 (g : Gate W1 W2) (ρ : Density (2^〚W1〛)) ,
      WF_Matrix (2^〚W1〛) (2^〚W1〛) ρ -> 〚boxed_gate g〛 ρ = 〚g〛 ρ.
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

Lemma lift_meas_correct : forall (ρ : Density 2), WF_Matrix 2 2 ρ
      -> 〚lift_meas〛 ρ = 〚boxed_gate meas〛 ρ.
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


