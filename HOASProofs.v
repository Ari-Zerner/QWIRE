Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.

Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.

(*****************************************************************************)
(** EXAMPLES START **)
(*****************************************************************************)

Lemma Ex : ⟦init true⟧ I1 = (|1⟩⟨1| : Density 2).
Proof.
  repeat (autounfold with den_db; simpl).
  Msimpl; reflexivity.
Qed.






Lemma WF_pad : forall m n (A : Square m),
      (m <= n)%nat ->
      WF_Matrix (2^m) (2^m) A ->
      WF_Matrix (2^n) (2^n) (@pad m n A).
Proof.
  intros. unfold pad.
  apply WF_kron; [ apply Nat.pow_nonzero; auto 
                 | apply Nat.pow_nonzero; auto 
                 | | | auto | show_wf].
  admit (* true *).
  admit (* true *).
Admitted.

Lemma apply_U_σ : forall m n (U : Square (2^m)),
      WF_Matrix (2^m) (2^m) U ->
      (m <= n)%nat -> 
      @apply_U m n U (σ_{n}) = super (pad n U).
Proof.
  intros. unfold apply_U.
  rewrite swap_list_n_id.
  apply WF_pad with (n := n) in H; auto.
  autorewrite with M_db.
  reflexivity.
Qed.



Lemma pad_nothing : forall m A,
      @pad m m A = A.
Proof.
  intros.
  unfold pad.
  rewrite Nat.sub_diag.
  simpl.
  autorewrite with M_db.
  reflexivity.
Qed.


(* TACTICS for doing this kind of proofs *)


Hint Rewrite hoas_to_db_pat_fresh_empty : proof_db.
Hint Rewrite denote_OCtx_fresh using validate : proof_db.

(* add some arithmetic *)
Hint Rewrite Nat.leb_refl : proof_db.
Hint Rewrite denote_pat_fresh_id : proof_db.
Hint Rewrite swap_fresh_seq : proof_db.
Hint Rewrite apply_U_σ pad_nothing using auto : proof_db.



Lemma id_circ_Id : forall W ρ, WF_Matrix (2^⟦W⟧) (2^⟦W⟧) ρ -> 
    ⟦@id_circ W⟧ ρ = ρ.
Proof.
  intros W ρ H.

  simpl. unfold denote_box. simpl.

  autorewrite with proof_db.
  rewrite super_I; auto.
Qed.
 
Lemma unitary_transpose_id_qubit : forall (U : Unitary Qubit), forall ρ,
   WF_Matrix (2^⟦Qubit⟧) (2^⟦Qubit⟧) ρ -> 
   ⟦unitary_transpose U⟧ ρ = ⟦@id_circ Qubit⟧ ρ.
Proof.
  intros U ρ pf_ρ.
  assert (unitary_U : is_unitary (denote_unitary U)) by apply unitary_gate_unitary.
  destruct unitary_U as [WF inv].
  repeat (autounfold with den_db; simpl in *).
  Msimpl.          
  repeat rewrite Mmult_assoc; try rewrite inv.
  repeat rewrite <- Mmult_assoc; try rewrite inv.
  Msimpl.          
  reflexivity.
Qed.


Lemma unitary_transpose_id : forall W (U : Unitary W) (ρ : Density (2^⟦W⟧ )),
  WF_Matrix (2^⟦W⟧) (2^⟦W⟧) ρ ->
  ⟦unitary_transpose U⟧ ρ = ⟦@id_circ W⟧ ρ.
Proof.
  intros W U ρ wfρ. 
  specialize (unitary_gate_unitary U); intros [WFU UU].
  simpl. autounfold with den_db. simpl.

  assert (wf_U : WF_Matrix (2^⟦W⟧) (2^⟦W⟧) (⟦U⟧)) by show_wf.
  assert (wf_U_dag : WF_Matrix (2^⟦W⟧) (2^⟦W⟧) (⟦U⟧†)) by show_wf.

  autorewrite with proof_db.

  repeat (simpl; autounfold with den_db).
  autorewrite with M_db.
  
  repeat rewrite <- Mmult_assoc.
  setoid_rewrite UU.
  repeat rewrite Mmult_assoc.
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

Definition uniform (n : nat) : Matrix n n :=
  fun x y => if (x =? y) && (x <? n) then 1/(INR n) else 0.

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

Lemma fair_toss : ⟦coin_flip⟧ I1  = fair_coin.
Proof.
  repeat (autounfold with den_db; simpl).
  Msimpl.
  prep_matrix_equality.
  autounfold with M_db.
  simpl; autorewrite with C_db.
  destruct_m_eq; autorewrite with C_db; reflexivity.
Qed.

Fixpoint upper_bound (li : list nat) : nat :=
  match li with
  | nil => 0
  | n :: li' => max (S n) (upper_bound li')
  end.

Lemma size_singleton : forall x w, size_Ctx (singleton x w) = 1%nat.
Proof.
  induction x; intros; simpl; auto.
Qed.

Lemma size_pat_to_ctx : forall {w} (p : Pat w) Γ, Types_Pat Γ p ->
    ⟦pat_to_ctx p⟧= ⟦w⟧.
Proof.
  induction 1; simpl; auto; try apply size_singleton.
  admit (* lemma about denote_OCtx (_ ⋓ _) *).
Admitted.


Lemma size_OCtx_WType : forall Γ w (p : Pat w), Types_Pat Γ p -> ⟦Γ⟧=⟦w⟧.
Admitted.

Lemma OCtx_dom_pat : forall w (p : Pat w),
      OCtx_dom (pat_to_ctx p) = pat_to_list p.
Admitted.

Lemma remove_refl : forall σ,
  fold_left (fun σ x => remove_var x σ) (get_σ σ) σ = st_{0}.
Admitted.



Lemma fresh_state_pat : forall w,
      fresh_state w ∅ ⊢ fresh_pat w ∅ :Pat.
Admitted.

(* Do these belong back in Denotation? *) 
Theorem inSeq_correct : forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2),
      Typed_Box g -> Typed_Box f ->
     ⟦inSeq f g⟧ = compose_super (⟦g⟧) (⟦f⟧).
Proof.
  intros W1 W2 W3 g f types_g types_f.
  autounfold with den_db; simpl. 

  destruct f as [f]. 
  destruct g as [g].
  autounfold with den_db; simpl.

  set (Γ1_0 := fresh_state W1 ∅).
  set (Γ2_0 := fresh_state W2 ∅).
  assert (⟦Γ1_0⟧ = ⟦W1⟧).
  { unfold Γ1_0.
    rewrite denote_OCtx_fresh; auto.
    validate. }
  assert (⟦Γ2_0⟧ = ⟦W2⟧).
  { unfold Γ2_0.
    rewrite denote_OCtx_fresh; auto.
    validate. }

  replace 0%nat with (⟦∅⟧:nat) by auto.
  replace (size_WType W1) with (⟦Γ1_0⟧) by auto.
  replace (size_WType W2) with (⟦Γ2_0⟧) by auto.


  apply denote_compose. 
  * apply types_f. apply fresh_state_pat. 
  * unfold Typed_Box in types_g. intros Γ Γ' p pf wf_p.
    solve_merge.
    apply types_g. monoid. auto.
  * type_check.
    apply is_valid_fresh. validate.
Qed.

Lemma merge_singleton_end : forall Γ w,
      Valid (Γ ++ [Some w]) = Valid Γ ⋓ singleton (length Γ) w.
Proof.
  Transparent merge.
  induction Γ as [ | [w' | ] Γ]; intros; simpl in *; auto.
  * rewrite <- IHΓ. reflexivity.
  * rewrite <- IHΓ. reflexivity.
  Opaque merge.
Qed.

Lemma fresh_state_decompose : forall w Γ,
      is_valid Γ ->
      fresh_state w Γ == Γ ∙ (pat_to_ctx (fresh_pat w Γ)).
Proof.
  induction w; intros;
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]);
    simpl.
  - solve_merge. apply merge_singleton_end.
  - solve_merge. apply merge_singleton_end.
  - solve_merge.
  - solve_merge.
    * repeat apply is_valid_fresh; auto.
    * destruct (IHw1 Γ); [auto | ].
      rewrite pf_merge.
      rewrite pf_merge in pf_valid.
      destruct (IHw2 (Γ ⋓ pat_to_ctx (fresh_pat w1 (Valid Γ)))); auto.
      rewrite pf_merge0.
      monoid.
Qed.

Close Scope circ_scope.
Lemma denote_tensor : forall (Γ Γ' : OCtx) {w} (c : Circuit w) 
                             {n1 n2} (ρ1 : Square n1) (ρ2 : Square n2),
      WF_Matrix (2^⟦Γ'⟧) (2^⟦Γ'⟧) ρ1 ->
      WF_Matrix (2^⟦Γ⟧) (2^⟦Γ⟧) ρ2 ->
      ⟨Γ | Γ' ⊩ c⟩ (ρ1 ⊗ ρ2) = (⟨∅ | Γ' ⊩ c⟩ ρ1) ⊗ ρ2.
Admitted.



Lemma hoas_to_db_pair : forall Γ w1 w2 (p1 : Pat w1) (p2 : Pat w2),
      hoas_to_db_pat Γ (pair p1 p2)
    = pair (hoas_to_db_pat Γ p1) (hoas_to_db_pat Γ p2).
Proof.
  intros. unfold hoas_to_db_pat. simpl.
  reflexivity.
Qed.



Theorem inPar_correct : forall W1 W1' W2 W2' (f : Box W1 W1') (g : Box W2 W2') 
     (ρ1 : Square (2^⟦W1⟧)) (ρ2 : Square (2^⟦W2⟧)),
     Typed_Box f -> Typed_Box g ->
     Mixed_State ρ1 -> Mixed_State ρ2 ->
     denote_box (inPar f g) (ρ1 ⊗ ρ2)%M = (denote_box f ρ1 ⊗ denote_box g ρ2)%M.
Proof.  
  intros W1 W1' W2 W2' f g ρ1 ρ2 types_f types_g mixed_ρ1 mixed_ρ2.

  destruct f as [f]. 
  destruct g as [g].
  repeat (autounfold with den_db; simpl).


  set (p_1 := fresh_pat W1 ∅).
  set (Γ_1 := fresh_state W1 ∅).
  set (p_2 := fresh_pat W2 Γ_1).
  set (Γ_2 := fresh_state W2 Γ_1).
  assert (Γ_1 ⊢ p_1 :Pat) by apply fresh_state_pat.
  assert (Γ_2 ⊢ p_2 :Pat) by admit (* need a vaiant of fresh_pat_typed *).

  replace 0%nat with (⟦∅⟧) by auto.
  replace (size_WType W1 + size_WType W2)%nat with (⟦Γ_2⟧).
  replace (size_WType W1) with (⟦Γ_1⟧).
  replace (size_WType W2) with (⟦fresh_state W2 ∅⟧).


  rewrite denote_compose with (Γ1' := Γ_2) (Γ1 := Γ_2) (Γ := Γ_1).
  set (Γ_3 := pat_to_ctx (fresh_pat W1' Γ_2)).

  rewrite denote_compose with (Γ1' := fresh_state W1' Γ_2) (Γ1 := Γ_3) (Γ := Γ_2).
  autounfold with den_db.
  repeat rewrite merge_nil_l.
  (*
  repeat rewrite denote_tensor.
  Search (⟨ _ | _ ⊩ output _ ⟩).
  rewrite denote_output.
  autorewrite with proof_db.*)
  admit (* stuck *). 
  * apply types_g; auto.
  * intros. type_check.
    unfold Γ_3.
    Search (pat_to_ctx) fresh_pat.
    admit (* need a variant of fresh_pat_typed *).
  * unfold Γ_3.
    assert (valid_Γ_2 : is_valid Γ_2) by admit.
    generalize (fresh_state_decompose W1' Γ_2 valid_Γ_2); intros assertion.
    solve_merge.
    rewrite pf_merge. monoid.
  * apply types_f; auto.
  * intros. type_check. apply types_g. auto.
  * admit (* this is not true... *).
  * rewrite denote_OCtx_fresh; auto. validate.
  * unfold Γ_1. rewrite denote_OCtx_fresh. auto. validate.
  * unfold Γ_2, Γ_1. repeat rewrite denote_OCtx_fresh. auto.
    validate. validate.
Admitted.



Open Scope circ_scope.

Lemma wf_biased_coin : forall c, WF_Matrix 2 2 (biased_coin c).
Proof.
  intros; show_wf.
Qed.

Hint Resolve wf_biased_coin : wf_db.
Hint Unfold super_Zero : den_db. 

Lemma flips_correct : forall n, ⟦coin_flips n⟧ I1 = biased_coin (1/(2^n)).
Proof.
  induction n.  
  + repeat (autounfold with den_db; simpl).
    Msimpl.
    prep_matrix_equality.
    autounfold with M_db.
    destruct_m_eq; clra.
  + simpl.
    repeat (simpl; autounfold with den_db). 
    replace 0%nat with (⟦∅⟧) by auto.
    rewrite denote_compose with (Γ := ∅) (Γ1 := ∅) (Γ1' := ∅);
    [ | apply unbox_typing; [type_check | apply coin_flips_WT]
    | type_check
    | solve_merge ].

       (* Apply IH *)
       rewrite denote_db_unbox in IHn.
       unfold fresh_pat in IHn.
       unfold fresh_state in IHn.
       rewrite merge_nil_r.
       unfold compose_super.
       rewrite IHn.


    (* Continue reducing *)
    repeat (autounfold with den_db; simpl).
    autorewrite with M_db. 
      
    setoid_rewrite kron_conj_transpose. 
    autorewrite with M_db.
    specialize hadamard_sa; intros pf_H.
    setoid_rewrite control_sa; auto.

    solve_matrix.
    * rewrite Cmult_comm.
      rewrite Cmult_assoc.
      autorewrite with C_db.
      rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
      replace (/ 2^n) with (/2 * /2 ^ n + /2 */2^n) at 1 by clra.
      rewrite Copp_plus_distr.
      repeat rewrite <- Cplus_assoc.
      autorewrite with C_db.
      reflexivity.
    * rewrite Cmult_comm.
      rewrite Cmult_assoc.
      autorewrite with C_db.
      rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
      reflexivity.
Qed.

Lemma cnot_eq : cnot = control σx.
Proof.
  autounfold with M_db.
  simpl.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; autorewrite with C_db; trivial).
Qed.

(***********)
(* sharing *)
(***********)

(*
Lemma denote_circuit_subst : forall w (c : Circuit w) Γ, Types_Circuit Γ c ->
      forall pad n σ, 
      WF_σ Γ (get_σ σ) ->
      ⟨ 
      ⟨ pad | n | c | σ ⟩ 
    = compose_super ⟨pad | n | c | st_{n}⟩
                    (super (swap_list n (get_σ σ))).
Proof.
  induction 1; intros.
  * simpl. 
    erewrite subst_id; eauto.
    admit. admit.
  * simpl. erewrite H; eauto. admit.

Admitted.

Lemma denote_unbox : forall n w1 w2 (b : Box w1 w2) Γ1 p σ, 
      Typed_Box b -> Types_Pat Γ1 p ->
      n = ⟦w1⟧ ->  WF_σ Γ1 (get_σ σ) ->

      ⟨0 | n | unbox b p | σ⟩
    = compose_super (⟦b⟧)
                    (super (swap_list (⟦w1⟧) (pat_to_list (subst_pat (get_σ σ) p)))).
Proof.
  intros.
  rewrite denote_db_unbox.
  rewrite denote_circuit_subst with (Γ := Γ1); auto.
  subst.
 admit (* not quite *).

Admitted.
*)
  
Hint Unfold apply_box : den_db.

Close Scope circ_scope.
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => Id 1
  | S n' => A ⊗ kron_n n' A
  end.
Notation "n ⨂ A" := (kron_n n A) : matrix_scope.
Open Scope circ_scope.

Open Scope matrix_scope.
Fixpoint prepare (ls : list nat) : Matrix 1%nat (2^(length ls)) :=
  fold_left (fun A x => ket x ⊗ A) ls (Id 1).

Definition pure {n} (vec : Matrix n 1%nat) : Matrix n n := vec × (vec †).

Definition prep α β : Matrix 2 2 := pure ((α.*|0⟩) .+ (β.*|1⟩)).
Lemma wf_prep : forall α β, WF_Matrix 2 2 (prep α β).
Proof.
  intros. unfold prep, pure.
  show_wf.
Qed.

Hint Unfold pure : den_db.


Lemma share_correct : forall n α β, 
      @denote _ _ (@Denote_Box _ _) (share n) (pure (α.*|0⟩ .+ β.*|1⟩))
    = pure (α.*(S n ⨂ |0⟩) .+ β.*(S n ⨂ |1⟩)).
Close Scope matrix_scope.
Proof.
  induction n; intros.
  * repeat (autounfold with den_db; simpl).
    autorewrite with M_db.
    reflexivity.
  * repeat (autounfold with den_db; simpl).
    autorewrite with M_db. 
    setoid_rewrite kron_conj_transpose.
    autorewrite with M_db. 

    remember (singleton 1%nat Qubit) as Γ_1.
    remember (singleton 0%nat Qubit) as Γ_2.
    remember (Γ_1 ⋓ Γ_2) as Γ_1'.

    assert (size_Γ_1_2 : ⟦Γ_1'⟧ = 2%nat).
    { subst. auto. }
    
    assert (Γ_2 ⊢ qubit 0%nat :Pat).
    { constructor. subst. constructor. }

    unfold add_fresh_state. simpl.
    unfold DBCircuits.get_fresh_var. simpl.
   
    replace 2%nat with (⟦Γ_1'⟧) by auto.
    replace (0%nat) with (⟦∅⟧) by auto. 
    replace (S (⟦∅⟧)) with 1%nat by auto.
    replace (Valid [Some Qubit; Some Qubit]) with Γ_1' by (subst; auto).
    

    rewrite denote_compose with (Γ := Γ_1) (Γ1 := Γ_2) (Γ1' := Γ_1');
    [ | apply share_WT; type_check; repeat constructor
    | intros; simpl; type_check
    | type_check ].
    Focus 2. Transparent merge. simpl. Opaque merge. validate.
    

    rewrite merge_nil_l.
    admit (* need padding lemma *).
Admitted.

(* Can we multiply 16 x 16 matrices? Yes, we can! 
Lemma test : ((swap ⊗ swap) × (swap ⊗ swap) = 'I_16)%M.
Proof. 
  solve_matrix. 
  all: unfold Nat.ltb; simpl; rewrite andb_false_r; reflexivity.
Qed. *)


(***********************)
(* Deutsch's Algorithm *)
(***********************)

Delimit Scope circ_scope with qc.

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

Close Scope circ_scope. 

Open Scope matrix_scope.
(* f(x) = 1. Unitary: Id ⊗ X *)
Definition f3 : Matrix 4 4 := Id 2 ⊗ σx.

Definition constant (U : Unitary (Qubit ⊗ Qubit)%qc) := 
                       denote_unitary U = f0 \/ denote_unitary U = f3.
Definition balanced (U : Unitary (Qubit ⊗ Qubit)%qc) := 
                       denote_unitary U = f1 \/ denote_unitary U = f2.

Lemma f2_WF : WF_Matrix 4 4 f2. Proof. show_wf. Qed.
Hint Resolve f2_WF : wf_db.
  
(* Set Ltac Profiling. *)

Lemma deutsch_constant : forall U_f, constant U_f -> 
                                ⟦U_deutsch U_f⟧ I1 = |0⟩⟨0|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  Msimpl.
  destruct H; rewrite H; clear.
  + (* f0 *)
    unfold f0.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
  + (* f3 *)
    unfold f3.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    reflexivity.
Qed.

Lemma deutsch_balanced : forall U_f, balanced U_f -> 
                                ⟦U_deutsch U_f⟧ I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  Msimpl.
  destruct H; rewrite H; clear.
  + (* f1 *)
    unfold f1.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
  + (* f2 *)
    unfold f2.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    reflexivity.
Qed.

(* Show Ltac Profile *)

(* Slightly faster to destruct 'balanced' last 
Lemma deutsch_balanced'' : forall U_f, balanced U_f -> 
                                ⟦deutsch U_f⟧ I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  Msimpl.
  solve_matrix.
  all: destruct H; rewrite H; clear.  
  + (* Cell (0,0), f1 *)
    unfold f1.
    autounfold with M_db.
    simpl.
    autorewrite with C_db.
    reflexivity.
  + (* Cell (0,0), f2 *)
    unfold f2.
    autorewrite with C_db.
    reflexivity.
  + (* Cell (1,1), f1 *)
    unfold f1.
    autounfold with M_db.
    simpl.
    autorewrite with C_db.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
  + (* Cell (1,1), f2 *)
    unfold f2.
    simpl.
    autorewrite with C_db.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
Qed.
*)


(*************************)
(* Quantum Teleportation *)
(*************************)


Definition EPR00 : Matrix 4 4 :=
  fun x y => match x, y with
             | 0, 0 => 1/2
             | 0, 3 => 1/2
             | 3, 0 => 1/2
             | 3, 3 => 1/2
             | _, _ => 0
             end.

Lemma bell00_spec :  ⟦bell00⟧ I1  = EPR00.
Proof.
  repeat (simpl; autounfold with den_db). 
  Msimpl. 
  solve_matrix.
Qed.

(* Works, but commented out for efficient compilation 
Definition M_alice (ρ : Matrix 4 4) : Matrix 4 4 :=
  fun x y => 
  match x, y with 
  | 0, 0 =>  (ρ 0%nat 0%nat + ρ 3%nat 0%nat + ρ 0%nat 3%nat + ρ 3%nat 3%nat) / 2
  | 1, 1 =>  (ρ 1%nat 1%nat + ρ 2%nat 1%nat + ρ 1%nat 2%nat + ρ 2%nat 2%nat) / 2
  | 2, 2 =>  (ρ 0%nat 0%nat - ρ 3%nat 0%nat - ρ 0%nat 3%nat + ρ 3%nat 3%nat) / 2
  | 3, 3 =>  (ρ 1%nat 1%nat - ρ 2%nat 1%nat - ρ 1%nat 2%nat + ρ 2%nat 2%nat) / 2
  | _, _ => 0
  end.

Lemma alice_spec : forall (ρ : Density 4), Mixed_State ρ -> ⟦alice⟧ ρ = M_alice ρ.
Proof.
  intros.
  repeat (simpl; autounfold with den_db). 
  specialize (WF_Mixed ρ H). intros WFρ.
  Msimpl.
  repeat rewrite <- Mmult_assoc.
  Msimpl.
  repeat rewrite Mmult_assoc.
  Msimpl.
  solve_matrix.
  + rewrite 2 (Cmult_comm (/√2)).
    rewrite <- 4 Cmult_plus_distr_r.
    rewrite <- Cmult_assoc.
    autorewrite with C_db.
    clra.
  + rewrite 2 (Cmult_comm (/√2)).
    rewrite <- 4 Cmult_plus_distr_r.
    rewrite <- Cmult_assoc.
    autorewrite with C_db.
    clra.
  + rewrite (Copp_mult_distr_r (/√2)).
    rewrite Copp_plus_distr.
    repeat rewrite Copp_mult_distr_l.
    rewrite 2 (Cmult_comm (/√2)).
    rewrite <- 4 Cmult_plus_distr_r.
    rewrite <- Cmult_assoc.
    autorewrite with C_db.
    clra.
  + rewrite (Copp_mult_distr_r (/√2)).
    rewrite Copp_plus_distr.
    repeat rewrite Copp_mult_distr_l.
    rewrite 2 (Cmult_comm (/√2)).
    rewrite <- 4 Cmult_plus_distr_r.
    rewrite <- Cmult_assoc.
    autorewrite with C_db.
    clra.
Qed.    

(* Spec computed rather than reasoned about *)
Definition M_bob (ρ : Density 8) : Density 2 := 
  fun x y => match x, y with
          | 0, 0 => ρ 0%nat 0%nat + ρ 3%nat 3%nat + ρ 4%nat 4%nat + ρ 7%nat 7%nat
          | 0, 1 => ρ 0%nat 1%nat + ρ 3%nat 2%nat - ρ 4%nat 5%nat - ρ 7%nat 6%nat
          | 1, 0 => ρ 1%nat 0%nat + ρ 2%nat 3%nat - ρ 5%nat 4%nat - ρ 6%nat 7%nat
          | 1, 1 => ρ 1%nat 1%nat + ρ 2%nat 2%nat + ρ 5%nat 5%nat + ρ 6%nat 6%nat
          | _, _ => 0
          end.

Lemma bob_spec : forall (ρ : Density 8), Mixed_State ρ -> ⟦bob⟧ ρ = M_bob ρ.
Proof.
  intros.
  repeat (simpl; autounfold with den_db). 
  specialize (WF_Mixed ρ H). intros WFρ.
  Msimpl.
  solve_matrix.
Qed.  

(* We convert the matrices back to functional representation for 
   unification. Simply comparing the matrices may be more efficient,
   however. *)

Lemma teleport_eq : forall (ρ : Density 2), 
  Mixed_State ρ -> ⟦teleport⟧ ρ = ρ.
Proof.
  intros ρ H.
  repeat (simpl; autounfold with den_db). 
  specialize (WF_Mixed _ H). intros WFρ.
  Msimpl.
  assoc_least.
  solve_matrix.
  all: rewrite (Cmult_assoc (/ √2));
       autorewrite with C_db;
       rewrite (Cmult_comm _ (/2));
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       reflexivity.
Qed.    

(* Teleport with Dynamic Lifting *)

Definition M_bob_distant (b1 b2 : bool) (ρ : Density 2) : Matrix 2 2 := 
  match b1, b2 with
  | true, true   => σz × σx × ρ × σx × σz  
  | true, false  => σz × ρ × σz  
  | false, true  => σx × ρ × σx  
  | false, false => ρ
  end.

Definition bob_distant_spec : forall b1 b2 (ρ : Density 2), 
    Mixed_State ρ -> 
    ⟦bob_distant b1 b2⟧ ρ = M_bob_distant b1 b2 ρ.
Proof.
  intros.
  specialize (WF_Mixed ρ H). intros WFρ.
  destruct b1, b2;
  repeat (simpl; autounfold with den_db); Msimpl; solve_matrix.
Qed.

Definition teleport_distant_eq : teleport_distant ≡ id_circ.
Proof. 
  repeat (autounfold with den_db; simpl).
  intros ρ H.
  unfold Splus.
  specialize (WF_Mixed _ H). intros WFρ.
  Msimpl.
  assoc_least.
  solve_matrix.
  all: rewrite (Cmult_assoc (/ √2));
       autorewrite with C_db;
       rewrite (Cmult_comm _ (/2));
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       reflexivity.
Qed.  

(* Lemmas out of date
Lemma boxed_gate_correct : forall W1 W2 (g : Gate W1 W2) (ρ : Density (2^⟦W1⟧)) ,
      Mixed_State ρ -> ⟦boxed_gate g⟧ ρ = ⟦g⟧ ρ.
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
  assert (wf_g : WF_Matrix (2^⟦W2⟧) (2^⟦W2⟧) (⟦g⟧ ρ)).
    generalize (WF_denote_gate 0 _ _ g ρ); intros.
    simpl in *. repeat rewrite mult_1_r in *. unfold denote_gate. apply (H wf_ρ).
  Msimpl.
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
      -> ⟦lift_eta Bit⟧ ρ = ⟦@id_circ Bit⟧ ρ.
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


*)