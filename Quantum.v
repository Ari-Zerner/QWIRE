Require Import Psatz.
Require Import Reals.

Require Export Prelim.
Require Export Complex.
Require Export Matrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

Definition ket0 : Matrix 2 1:= 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition ket1 : Matrix 2 1 := 
  fun x y => match x, y with 
          | 0, 0 => C0
          | 1, 0 => C1
          | _, _ => C0
          end.

Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ket0 else ket1.
Transparent ket0.
Transparent ket1.
Transparent ket.

Notation "|0⟩" := ket0.
Notation "|1⟩" := ket1.
Notation "⟨0|" := ket0†.
Notation "⟨1|" := ket1†.
Notation "|0⟩⟨0|" := (|0⟩×⟨0|).
Notation "|1⟩⟨1|" := (|1⟩×⟨1|).
Notation "|1⟩⟨0|" := (|1⟩×⟨0|).
Notation "|0⟩⟨1|" := (|0⟩×⟨1|).

Definition hadamard : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => 0
          end).

Fixpoint hadamard_k (k : nat) : Matrix (2^k) (2^k):= 
  match k with
  | 0 => Id 1
  | S k' => hadamard ⊗ hadamard_k k'
  end. 

Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. apply kron_1_r. Qed.

(* Alternative definitions:
Definition pauli_x : Matrix 2 2 := fun x y => if x + y =? 1 then 1 else 0.
Definition pauli_y : Matrix 2 2 := fun x y => if x + y =? 1 then (-1) ^ x * Ci else 0.
Definition pauli_z : Matrix 2 2 := fun x y => if (x =? y) && (x <? 2) 
                                           then (-1) ^ x * Ci else 0.
*)

Definition σx : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => C1
          | 1, 0 => C1
          | _, _ => C0
          end.

Definition σy : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => -Ci
          | 1, 0 => Ci
          | _, _ => C0
          end.

Definition σz : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => -C1
          | _, _ => C0
          end.
  
Definition control {n : nat} (A : Matrix n n) : Matrix (2*n) (2*n) :=
  fun x y => if (x <? n) && (y =? x) then 1 else 
          if (n <=? x) && (n <=? y) then A (x-n)%nat (y-n)%nat else 0.

(* Definition cnot := control pauli_x. *)
(* Direct definition makes our lives easier *)
Definition cnot : Matrix 4 4 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 3 => C1
          | 3, 2 => C1
          | _, _ => C0
          end.          

Lemma cnot_eq : cnot = control σx.
Proof.
  unfold cnot, control, σx.
  solve_matrix.
Qed.

(* Swap Matrices *)

Definition swap : Matrix 4 4 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 2 => C1
          | 2, 1 => C1
          | 3, 3 => C1
          | _, _ => C0
          end.

(* Rotation Matrices (theta, phi, lambda) := Rz(phi) Ry(theta) Rz(lambda) *)

Definition rotation (theta phi lambda : FakeR) : Matrix 2 2 :=
  let t := (FakeRtoR theta) in
  let p := (FakeRtoR phi) in
  let l := (FakeRtoR lambda) in
  (fun x y => match x, y with
        | 0, 0 => (cos((p + l) / 2) - Ci * sin((p + l) / 2)) * cos (t / 2)
        | 0, 1 => -(cos((p - l) / 2) - Ci * sin((p - l) / 2)) * sin (t / 2)
        | 1, 0 => (cos((p - l) / 2) + Ci * sin((p - l) / 2)) * sin (t / 2)
        | 1, 1 => (cos((p + l) / 2) + Ci * sin((p + l) / 2)) * cos (t / 2)
        | _, _ => 0
        end).

(* Does this overwrite the other Hint DB M? *)
Hint Unfold ket0 ket1 hadamard σx σy σz control cnot swap : M_db.

(* Lemmas *)
Lemma MmultX1 : σx × |1⟩ = |0⟩. Proof. solve_matrix. Qed.
Lemma Mmult1X : ⟨1| × σx = ⟨0|. Proof. solve_matrix. Qed.
Lemma MmultX0 : σx × |0⟩ = |1⟩. Proof. solve_matrix. Qed.
Lemma Mmult0X : ⟨0| × σx = ⟨1|. Proof. solve_matrix. Qed.
Hint Rewrite Mmult0X Mmult1X MmultX0 MmultX1 : M_db.

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


Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. omega. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.

Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try omega 
  end.

(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
(* Requires: i + 1 < n *)
Fixpoint swap_to_0_aux (n i : nat) {struct i} : Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' =>  (Id (2^i) ⊗ swap ⊗ Id (2^(n-i-2))) × (* swap i-1 with i *)
            swap_to_0_aux n i' × 
            (Id (2^i) ⊗ swap ⊗ Id (2^(n-i-2))) (* swap i-1 with 0 *)
  end.

(* Requires: i < n *)
Definition swap_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => Id (2^n) 
  | S i' => swap_to_0_aux n i'
  end.
  
(* Swapping qubits i and j in an n-qubit system, where i < j *) 
(* Requires i < j, j < n *)
Fixpoint swap_two_aux (n i j : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => swap_to_0 n j 
  | S i' => Id 2 ⊗ swap_two_aux (n-1) (i') (j-1)
  end.

(* Swapping qubits i and j in an n-qubit system *)
(* Requires i < n, j < n *)
Definition swap_two (n i j : nat) : Matrix (2^n) (2^n) :=
  if i =? j then Id (2^n) 
  else if i <? j then swap_two_aux n i j
  else swap_two_aux n j i.

(* Simpler version of swap_to_0 that shifts other elements *)
(* Requires: i+1 < n *)
Fixpoint move_to_0_aux (n i : nat) {struct i}: Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' => (move_to_0_aux n i') × (Id (2^i) ⊗ swap ⊗ Id (2^(n-i-2))) 
                  
  end.
             
(* Requires: i < n *)
Definition move_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => Id (2^n) 
  | S i' => move_to_0_aux n i'
  end.
 
(* Always moves up in the matrix from i to k *)
(* Requires: k < i < n *)
Fixpoint move_to (n i k : nat) : Matrix (2^n) (2^n) := 
  match k with 
  | O => move_to_0 n i 
  | S k' => Id 2 ⊗ move_to (n-1) (i-1) (k')
  end.

(*
Eval compute in ((swap_two 1 0 1) 0 0)%nat.
Eval compute in (print_matrix (swap_two 1 0 2)).
*)

(** Well Formedness of Quantum States and Unitaries **)

Lemma WF_bra0 : WF_Matrix 1 2 ⟨0|. Proof. show_wf. Qed.
Lemma WF_bra1 : WF_Matrix 1 2 ⟨1|. Proof. show_wf. Qed.
Lemma WF_ket0 : WF_Matrix 2 1 |0⟩. Proof. show_wf. Qed.
Lemma WF_ket1 : WF_Matrix 2 1 |1⟩. Proof. show_wf. Qed.
Lemma WF_braket0 : WF_Matrix 2 2 |0⟩⟨0|. Proof. show_wf. Qed.
Lemma WF_braket1 : WF_Matrix 2 2 |1⟩⟨1|. Proof. show_wf. Qed.

Hint Resolve WF_bra0 WF_bra1 WF_ket0 WF_ket1 WF_braket0 WF_braket1 : wf_db.

Lemma WF_hadamard : WF_Matrix 2 2 hadamard. Proof. show_wf. Qed.
Lemma WF_σx : WF_Matrix 2 2 σx. Proof. show_wf. Qed.
Lemma WF_σy : WF_Matrix 2 2 σy. Proof. show_wf. Qed.
Lemma WF_σz : WF_Matrix 2 2 σz. Proof. show_wf. Qed.
Lemma WF_cnot : WF_Matrix 4 4 cnot. Proof. show_wf. Qed.
Lemma WF_swap : WF_Matrix 4 4 swap. Proof. show_wf. Qed.

Lemma WF_rotation : forall (t p l : FakeR), WF_Matrix 2 2 (rotation t p l).
Proof.
  intros t p l x y H1. destruct H1 as [H2 | H2].
  - destruct H2 eqn:Hx.
    + reflexivity.
    + simpl. destruct m eqn:Heqm.
      * inversion H2. inversion H0.
      * reflexivity. 
  - destruct x eqn:Hx.
    + destruct H2 eqn:Hy.
      * reflexivity.
      * simpl. destruct m; [inversion g | reflexivity].
    + destruct H2 eqn:Hy.
      * destruct n; reflexivity.
      * destruct n; try reflexivity.
        destruct m; [inversion g | reflexivity].
Qed.

Lemma WF_control : forall (n m : nat) (U : Matrix n n), 
      (m = 2 * n)%nat ->
      WF_Matrix n n U -> WF_Matrix m m (control U).
Proof.
  intros n m U E WFU. subst.
  unfold control, WF_Matrix in *.
  intros x y [Hx | Hy];
  bdestruct (x <? n); bdestruct (y =? x); bdestruct (n <=? x); bdestruct (n <=? y);
    simpl; try reflexivity; try omega. 
  all: rewrite WFU; [reflexivity|omega].
Qed.

Hint Resolve WF_hadamard WF_σx WF_σy WF_σz WF_cnot WF_swap WF_control : wf_db.

(** Unitaries are unitary **)

Definition is_unitary {n: nat} (U : Matrix n n): Prop :=
  WF_Matrix n n U /\ U † × U = Id n.

Hint Unfold is_unitary : M_db.

(* More precise *)
(* Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†. *)

Lemma H_unitary : is_unitary hadamard.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  autounfold with M_db.
  destruct x as [| [|x]]; destruct y as [|[|y]]; simpl; autorewrite with C_db; 
    try reflexivity.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  reflexivity.
Qed.

Lemma σx_unitary : is_unitary σx.
Proof. 
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σy_unitary : is_unitary σy.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σz_unitary : is_unitary σz.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma control_unitary : forall n (A : Matrix n n), 
                          is_unitary A -> is_unitary (control A). 
Proof.
  intros n A.
  split.
  destruct H; auto with wf_db.
  induction n.
  + unfold control, is_unitary, conj_transpose, Mmult, Id.
    prep_matrix_equality.
    replace (x <? 0) with false by reflexivity.
    rewrite andb_false_r.
    reflexivity.
  + unfold control, is_unitary, Mmult, Id.
    prep_matrix_equality.    
    simpl.

(*
  intros.
  unfold control.
  prep_matrix_equality.
  unfold conj_transpose, Mmult, Id in *.
  destruct (x <? n) eqn:Ltxn, (y <? n) eqn:Ltyn.
  simpl.
*)    

Admitted.

Lemma transpose_unitary : forall n (A : Matrix n n), is_unitary A -> is_unitary (A†).
  intros. 
  simpl.
  split.
  + destruct H; auto with wf_db.
  + unfold is_unitary in *.
    rewrite conj_transpose_involutive.
    destruct H as [_ H].
    apply Minv_left in H as [_ S]. (* NB: Admitted lemma *)
    assumption.
Qed.

Lemma cnot_unitary : is_unitary cnot.
Proof.
  split. 
  apply WF_cnot.
  unfold Mmult, Id.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma id_unitary : forall n, is_unitary (Id n). 
Proof.
  split.
  apply WF_Id.
  unfold is_unitary.
  rewrite id_conj_transpose_eq.
  apply Mmult_1_l.
  apply WF_Id.
Qed.

Lemma swap_unitary : is_unitary swap.
Proof. 
  split.
  apply WF_swap.
  unfold is_unitary, Mmult, Id.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma rotation_unitary : forall (t p l : FakeR), is_unitary (rotation t p l).
Proof.
  split.
  show_wf.
  unfold Mmult, Id, rotation.
  prep_matrix_equality.
  destruct x as [| [|x]].
  - destruct y as [|[|y]].
    + Admitted.
  
Lemma kron_unitary : forall {m n} (A : Matrix m m) (B : Matrix n n),
  is_unitary A -> is_unitary B -> is_unitary (A ⊗ B).
Admitted.

Lemma unitary_swap_to_0 : forall n i, (i < n)%nat -> is_unitary (swap_to_0 n i).
Proof.
  intros n i.
  generalize dependent n.
  unfold is_unitary; split.
  + (* well-formedness *)
    induction i. 
    simpl. auto with wf_db.     
    simpl in *.
    unfold swap_to_0 in IHi.
    destruct i; simpl in *.
    - specialize Nat.pow_nonzero; intros NZ.
      replace (2 ^ n)%nat with (4 * 2^(n-2))%nat by unify_pows_two.
      auto with wf_db.
    - specialize Nat.pow_nonzero; intros NZ.
      replace (2^n)%nat with  (2 ^ (i+1) * 4 * 2 ^ (n - i - 3))%nat by unify_pows_two.    
      auto with wf_db.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (i + 1))%nat by unify_pows_two.
      replace (n - S i - 2)%nat with (n - i - 3)%nat by omega. 
      apply WF_mult; auto with wf_db.
      apply WF_mult; auto with wf_db.
      replace (2 ^ (i + 1) * 4 * 2 ^ (n - i - 3))%nat with (2^n)%nat by unify_pows_two.
      apply IHi.
      omega.
  + induction i; simpl.
    - apply id_unitary.
    - unfold swap_to_0 in IHi. 
      destruct i.
      * simpl.
        remember ( Id (2 ^ (n - 2))) as A.
        remember swap as B.
        setoid_rewrite (kron_conj_transpose _ _ _ _ B A).            
    
(*    rewrite (kron_mixed_product B† A† B A). *)

        specialize (kron_mixed_product _ _ _ _ _ _ B† A† B A); intros H'.
        assert (is_unitary B). subst. apply swap_unitary.
        assert (is_unitary A). subst. apply id_unitary.
        destruct H0 as [_ H0], H1 as [_ H1].
        rewrite H0 in H'.
        rewrite H1 in H'.
        replace (Id (2 ^ n)) with (Id 4 ⊗ Id (2 ^ (n - 2))).
        (* apply H doesn't work. 
         Surprisingly, that's the matrix types failing to line up *)
        rewrite <- H'.
        replace (4 * (2 ^ (n - 2)))%nat with (2 ^ n)%nat.
        reflexivity.
        unify_pows_two.
        unify_pows_two.
        replace (2^n)%nat with (2^2 * 2^(n-2))%nat by unify_pows_two.
        rewrite id_kron.
        reflexivity.
      * simpl.
Admitted.

Lemma unitary_swap_two : forall n i j, (i < n)%nat -> (j < n)%nat ->
                                  is_unitary (swap_two n i j).
Proof.
  intros n i j P1 P2.
  unfold is_unitary.
  unfold swap_two.
  destruct (lt_eq_lt_dec i j) as [[ltij | eq] | ltji].
  + induction i.
    simpl.
Admitted.

(* Our unitaries are self-adjoint *)

Definition id_sa := id_conj_transpose_eq.

Lemma hadamard_sa : hadamard† = hadamard.
Proof.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma σx_sa : σx† = σx.
Proof. 
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma σy_sa : σy† = σy.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma σz_sa : σz† = σz.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma cnot_sa : cnot† = cnot.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma swap_sa : swap† = swap.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma control_sa : forall (n : nat) (A : Square n), 
    A† = A -> (control A)† = (control A).
Proof.
  intros n A H.
  prep_matrix_equality.
  autounfold with M_db in *.
  autounfold with M_db in *.
  bdestruct (x =? y); bdestruct (y =? x); 
  bdestruct (y <? n); bdestruct (x <? n); 
  bdestruct (n <=? y); bdestruct (n <=? x); 
    try omega; simpl; try clra.
  subst. 
  (* ah, rewriting at X *)
  remember (Cconj (A (y - n)%nat (y - n)%nat)) as L.
  rewrite <- H. subst.
  reflexivity.
  remember (Cconj (A (y - n)%nat (x - n)%nat)) as L. (* oh hackyness *)
  rewrite <- H. subst.
  reflexivity.
Qed.  

Lemma braket0_sa : |0⟩⟨0|† = |0⟩⟨0|. Proof. mlra. Qed.
Lemma braket1_sa : |1⟩⟨1|† = |1⟩⟨1|. Proof. mlra. Qed.

Hint Rewrite hadamard_sa σx_sa σy_sa σz_sa cnot_sa swap_sa 
             braket1_sa braket0_sa : M_db.

Hint Rewrite control_sa using (autorewrite with M_db; reflexivity) : M_db.


(* Pure and Mixed States *)

(* Wiki:
In operator language, a density operator is a positive semidefinite, hermitian 
operator of trace 1 acting on the state space. A density operator describes 
a pure state if it is a rank one projection. Equivalently, a density operator ρ 
describes a pure state if and only if ρ = ρ ^ 2 
Hence a quantum state state should be:
  positive-semidefinite = z†Az >= 0 for any column vector z. 
  hermitian = self-adjoint
  trace 1
*)

(* We need an additional restriction that trace = 1 to
   exclude the identity and zero matrices. *)

Notation Density n := (Matrix n n) (only parsing). 

(* don't have positive-semidefinite yet *)
Definition Pure_State {n} (ρ : Density n) : Prop := 
  WF_Matrix n n ρ /\ trace ρ = 1 /\ ρ = ρ†  /\ ρ = ρ × ρ.

Lemma pure0 : Pure_State |0⟩⟨0|. 
Proof. unfold Pure_State. repeat split. auto with wf_db. clra. mlra. mlra. Qed.
Lemma pure1 : Pure_State |1⟩⟨1|. 
Proof. unfold Pure_State. repeat split. auto with wf_db. clra. mlra. mlra. Qed.

(* Wiki:
For a finite-dimensional function space, the most general density operator 
is of the form:

  ρ =∑_j p_j |ψ_j⟩⟨ ψ_j| 

where the coefficients p_j are non-negative and add up to one. *)

Inductive Mixed_State {n} : (Matrix n n) -> Prop :=
| Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
| Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> Mixed_State ρ1 -> Mixed_State ρ2 ->
                                       Mixed_State (p .* ρ1 .+ (1-p)%R .* ρ2).  

Lemma WF_Pure : forall {n} (ρ : Density n), Pure_State ρ -> WF_Matrix n n ρ.
Proof. unfold Pure_State. intuition. Qed.
Hint Resolve WF_Pure : wf_db.
Lemma WF_Mixed : forall {n} (ρ : Density n), Mixed_State ρ -> WF_Matrix n n ρ.
Proof. induction 1; auto with wf_db. Qed.
Hint Resolve WF_Mixed : wf_db.

(** Density matrices and superoperators **)

Definition Superoperator m n := Density m -> Density n.

Definition WF_Superoperator {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

(* Transparent Density. *)

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.

Lemma super_I : forall n ρ,
      WF_Matrix n n ρ ->
      super ('I_n) ρ = ρ.
Proof.
  intros.
  unfold super.
  autorewrite with M_db.
  reflexivity.
Qed.

Definition compose_super {m n p} (g : Superoperator n p) (f : Superoperator m n)
                      : Superoperator m p :=
  fun ρ => g (f ρ).
Lemma compose_super_correct : forall {m n p} 
                              (g : Superoperator n p) (f : Superoperator m n),
      WF_Superoperator g -> WF_Superoperator f ->
      WF_Superoperator (compose_super g f).
Proof.
  intros m n p g f pf_g pf_f.
  unfold WF_Superoperator.
  intros ρ mixed.
  unfold compose_super.
  apply pf_g. apply pf_f. auto.
Qed.

Definition sum_super {m n} (f g : Superoperator m n) : Superoperator m n :=
  fun ρ => (1/2)%R .* f ρ .+ (1 - 1/2)%R .* g ρ.
Lemma WF_sum_super : forall m n (f g : Superoperator m n),
      WF_Superoperator f -> WF_Superoperator g -> WF_Superoperator (sum_super f g).
Proof.
  intros m n f g wf_f wf_g ρ pf_ρ.
  unfold sum_super. 
  set (wf_f' := wf_f _ pf_ρ).
  set (wf_g' := wf_g _ pf_ρ).
  apply (Mix_S (1/2) (f ρ) (g ρ)); auto. 
  lra.
Qed.

Definition SZero {n} : Superoperator n n := fun ρ => Zero n n.
Definition Splus {m n} (S T : Superoperator m n) : Superoperator m n :=
  fun ρ => S ρ .+ T ρ.

Definition new0_op : Superoperator 1 2 := super |0⟩.
Definition new1_op : Superoperator 1 2 := super |1⟩.
Definition meas_op : Superoperator 2 2 := fun ρ => super |0⟩⟨0| ρ .+ super |1⟩⟨1| ρ.
Definition discard_op : Superoperator 2 1 := fun ρ => super ⟨0| ρ .+ super ⟨1| ρ.

Lemma pure_unitary : forall {n} (U ρ : Matrix n n), 
  is_unitary U -> Pure_State ρ -> Pure_State (super U ρ).
Proof.
  intros n U ρ [WFU H] [WFρ [trP [SA SQ]]].
  unfold Pure_State, is_unitary, super in *.
  intuition.
  + (* I don't actually know how to prove this *)
    rewrite SQ.
    autounfold with M_db; simpl.    
    admit.
  + autorewrite with M_db.
    rewrite <- SA.
    rewrite Mmult_assoc.
    reflexivity.
  + remember (U × ρ × (U) † × (U × ρ × (U) †)) as rhs.
    rewrite SQ.
    replace (ρ × ρ) with (ρ × Id n × ρ) by (rewrite Mmult_1_r; trivial).
    rewrite <- H.
    rewrite Heqrhs.
    repeat rewrite Mmult_assoc. 
    reflexivity.
Admitted.

Lemma pure_hadamard_1 : Pure_State (super hadamard |1⟩⟨1|).
Proof. apply pure_unitary. 
       + apply H_unitary.       
       + apply pure1. 
Qed.

Definition dm12 : Matrix 2 2 :=
  (fun x y => match x, y with
          | 0, 0 => 1 / 2
          | 0, 1 => 1 / 2
          | 1, 0 => 1 / 2
          | 1, 1 => 1 / 2
          | _, _ => 0
          end).

Lemma pure_dm12 : Pure_State dm12. Proof.
  unfold Pure_State. repeat split.
  show_wf.
  unfold dm12; simpl; clra.  
  unfold dm12; solve_matrix.
  unfold dm12; solve_matrix.
Qed.

Lemma mixed_meas_12 : Mixed_State (meas_op dm12).
Proof. unfold meas_op. 
       replace (super |0⟩⟨0| dm12) with ((1/2)%R .* |0⟩⟨0|) 
         by (unfold dm12, super; mlra).
       replace (super |1⟩⟨1| dm12) with ((1 - 1/2)%R .* |1⟩⟨1|) 
         by (unfold dm12, super; mlra).
       apply Mix_S.
       lra.       
       constructor; apply pure0.
       constructor; apply pure1.
Qed.

Lemma mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Matrix n n U -> is_unitary U -> Mixed_State ρ -> Mixed_State (super U ρ).
Proof.
  intros n U ρ WFU H M.
  induction M.
  + apply Pure_S.
    apply pure_unitary; trivial.
  + unfold is_unitary, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply Mix_S; trivial.
Qed.

Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ -> trace ρ = 1.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H; intuition.
  + rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    rewrite IHMixed_State1, IHMixed_State2.
    clra.
Qed.

Lemma mixed_state_diag_real : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        snd (ρ i i) = 0.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H; intuition. 
    assert (ρ i i = ρ † i i) by (rewrite <- H1; reflexivity).
    unfold conj_transpose, Cconj in H2.
    replace (ρ i i) with (fst (ρ i i), snd (ρ i i)) in H2 by clra. 
    simpl in H2.
    inversion H2.
    lra.
  + simpl.
    rewrite IHMixed_State1, IHMixed_State2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.

Lemma pure_id1 : Pure_State ('I_ 1).
Proof.
  unfold Pure_State. repeat split. 
  auto with wf_db. 
  clra. 
  autorewrite with M_db; reflexivity. 
  autorewrite with M_db; reflexivity. 
Qed.

Lemma pure_dim1 : forall (ρ : Square 1), Pure_State ρ -> ρ = 'I_ 1.
Proof.
  intros ρ [WFP [TRP [SA PPP]]].
  prep_matrix_equality.
  destruct x.
  destruct y.  
  + unfold trace in TRP; simpl in TRP.
    rewrite Cplus_0_l in TRP.
    rewrite TRP; reflexivity.
  + rewrite WFP, WF_Id; trivial; omega.
  + rewrite WFP, WF_Id; trivial; omega.
Qed.    

Lemma mixed_dim1 : forall (ρ : Square 1), Mixed_State ρ -> ρ = 'I_ 1.
Proof.
  intros.  
  induction H.
  + apply pure_dim1; trivial.
  + rewrite IHMixed_State1, IHMixed_State2.
    prep_matrix_equality.
    clra.
Qed.  

(************
 *Automation*
 ************)

(* For when autorewrite needs some extra help *)

Ltac Msimpl := 
  repeat match goal with 
  | [ |- context[(?A ⊗ ?B)†]]    => let H := fresh "H" in 
                                  specialize (kron_conj_transpose _ _ _ _ A B) as H;
                                  simpl in H; rewrite H; clear H
  | [ |- context[(control ?U)†]] => let H := fresh "H" in 
                                  specialize (control_sa _ U) as H;
                                  simpl in H; rewrite H; 
                                  [clear H | Msimpl; reflexivity]
  | [|- context[(?A ⊗ ?B) × (?C ⊗ ?D)]] => 
                                  let H := fresh "H" in 
                                  specialize (kron_mixed_product _ _ _ _ _ _ A B C D);
                                  intros H; simpl in H; rewrite H; clear H
  | _                         => autorewrite with M_db
  end.

(**************
 *Swap testing*
 **************)

Lemma swap_spec : forall (q q' : Matrix 2 1), WF_Matrix 2 1 q -> 
                                         WF_Matrix 2 1 q' ->
                                         swap × (q ⊗ q') = q' ⊗ q.
Proof.
  intros q q' WF WF'.
  solve_matrix.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' O (S y)) by omega.
    clra.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' O (S y)) by omega.
    clra.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' 1%nat (S y)) by omega.
    clra.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' 1%nat (S y)) by omega.
    clra.
Qed.  

Lemma kron_assoc : forall (m n o p q r : nat) (A : Matrix m n) (B : Matrix o p) 
  (C : Matrix q r), (A ⊗ B ⊗ C) = A ⊗ (B ⊗ C).
Admitted.

Lemma swap_to_0_test_24 : forall (q0 q1 q2 q3 : Matrix 2 1), 
  WF_Matrix 2 1 q0 -> WF_Matrix 2 1 q1 -> WF_Matrix 2 1 q2 -> WF_Matrix 2 1 q3 ->
  swap_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q1 ⊗ q0 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold swap_to_0, swap_to_0_aux.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc _ _ _ _ _ _ q0 q1).
  rewrite kron_mixed_product.
  rewrite (kron_mixed_product _ _ _ _ _ _ ('I_ (2^1)) swap).
  rewrite swap_spec by assumption.
  Msimpl.
  rewrite (kron_assoc _ _ _ _ _ _ q0).
  rewrite (kron_assoc _ _ _ _ _ _ q2 q1).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ q0 q2 (q1 ⊗ q3)).
  simpl.
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ swap ('I_4) (q0 ⊗ q2) (q1 ⊗ q3)).
  rewrite swap_spec by assumption.
  Msimpl.
  rewrite (kron_assoc _ _ _ _ _ _ q2 q0).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ q0 q1 q3).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ('I_2)).  
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ ('I_2) (swap ⊗ 'I_2) q2 _).
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ swap ('I_2) _ _).
  Msimpl.
  rewrite swap_spec by assumption.
  repeat setoid_rewrite kron_assoc.
  reflexivity.
Qed.

(* To define for general lemma *)
Parameter big_kron : forall (m n : nat) (l : list (Matrix m n)), 
  Matrix (m^(length l)) (n^(length l)).

Lemma swap_to_0_spec : forall (q q0 : Matrix 2 1) (n k : nat) (l1 l2 : list (Matrix 2 1)), 
   length l1 = (k - 1)%nat ->
   length l2 = (n - k - 2)%nat ->   
   @Mmult (2^n) (2^n) 1 (swap_to_0 n k) (big_kron 2 1 ([q0] ++ l1 ++ [q] ++ l2)) = 
     big_kron 2 1 ([q] ++ l1 ++ [q0] ++ l2).
Admitted.

Lemma swap_two_base : swap_two 2 1 0 = swap.
Proof. unfold swap_two. simpl. apply kron_1_r. Qed.

Lemma swap_second_two : swap_two 3 1 2 = Id 2 ⊗ swap.
Proof. unfold swap_two.
       simpl.
       rewrite kron_1_r.
       reflexivity.
Qed.

Lemma swap_0_2 : swap_two 3 0 2 = ('I_2 ⊗ swap) × (swap ⊗ 'I_2) × ('I_2 ⊗ swap).
Proof.
  unfold swap_two.
  simpl.
  Msimpl.
  reflexivity.
Qed.

Lemma swap_two_spec : forall (q q0 : Matrix 2 1) (n0 n1 n2 n k : nat) (l0 l1 l2 : list (Matrix 2 1)), 
   length l0 = n0 ->
   length l1 = n1 ->
   length l2 = n2 ->   
   n = (n0 + n1 + n2 + 2)%nat ->
   @Mmult (2^n) (2^n) 1 
     (swap_two n n0 (n0+n1+1)) (big_kron 2 1 (l0 ++ [q0] ++ l1 ++ [q] ++ l2)) = 
     big_kron 2 1 (l0 ++ [q] ++ l1 ++ [q0] ++ l2).
Admitted.

Lemma move_to_0_test_24 : forall (q0 q1 q2 q3 : Matrix 2 1), 
  WF_Matrix 2 1 q0 -> WF_Matrix 2 1 q1 -> WF_Matrix 2 1 q2 -> WF_Matrix 2 1 q3 ->
  move_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q0 ⊗ q1 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold move_to_0, move_to_0_aux.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc _ _ _ _ _ _ q0 q1).
  simpl.
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ (('I_2) ⊗ swap) ('I_2) 
                                     (q0 ⊗ (q1 ⊗ q2)) q3).
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ ('I_2) swap q0 (q1 ⊗ q2)).
  Msimpl.
  rewrite swap_spec by assumption.
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ q0 q2 q1).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ (q0 ⊗ q2) q1 q3).
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ swap ('I_4) (q0 ⊗ q2) (q1 ⊗ q3)).
  rewrite swap_spec by assumption.
  Msimpl.
  repeat setoid_rewrite kron_assoc.
  reflexivity.
Qed.


(* *)