Require Import HOASCircuits.
Require Import Prelim.
Require Import Denotation.
Require Import TypeChecking.
Require Import HOASLib.
Require Import SemanticLib.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

(* Note: All of these circuits should in principle end with an arbitrary circuit -
         here I'm just outputting the mentioned (qu)bits *)

Open Scope circ_scope.  

(** Equality 1: X; meas = meas; NOT **)

Definition X_meas : Box Qubit Bit :=
  box_ q ⇒ 
    let_ q ← X $ q;
    let_ b ← meas $ q;
    b.
Lemma X_meas_WT : Typed_Box X_meas.
Proof. type_check. Qed.

Definition meas_NOT : Box Qubit Bit := 
  box_ q ⇒ BNOT $ meas $ q.

Lemma meas_NOT_WT : Typed_Box meas_NOT.
Proof. type_check. Qed.

Lemma NOT_meas_comm : X_meas ≡ meas_NOT.
Proof.
  matrix_denote.
  intros ρ b M.
  Msimpl.
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_r.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite (Mmult_assoc _ _ _ _ _ ⟨0| σx).
  repeat rewrite (Mmult_assoc _ _ _ _ _ ⟨1| σx).
  repeat rewrite (Mmult_assoc _ _ _ _ _ σx |0⟩).
  repeat rewrite (Mmult_assoc _ _ _ _ _ σx |1⟩).
  Msimpl.
  rewrite Mplus_comm.
  reflexivity.
Qed.

(** Equality 2: meas x; lift x; if x then U else b = alt x U V; meas-discard x **) 

Definition lift_UV {W} (U V : Unitary W) : Box (Qubit ⊗ W) W :=
  box_ qr ⇒ 
    let_ (q,r) ← output qr;
    let_ b ← meas $ q;
    lift_ x ← b;
    if x then U $ r else V $ r.
Lemma lift_UV_WT : forall W (U V : Unitary W), Typed_Box (lift_UV U V).
Proof. type_check. Qed.

Definition alternate {W} (U V : Unitary W) : Box (Qubit ⊗ W) (Qubit ⊗ W) :=
  box_ cx ⇒ 
    let_ (c,x) ← ctrl U $ cx;
    let_ c     ← X $ c;
    let_ (c,x) ← ctrl V $ (c,x);
    (X $ c,x).
Lemma alternate_WT : forall W (U V : Unitary W), Typed_Box (alternate U V).           
Proof. type_check. Qed.

Definition alt_UV {W} (U V : Unitary W) : Box (Qubit ⊗ W) W :=     
  box_ (q,r) ⇒ 
    let_ (q,r) ← alternate U V $ (q,r);
    let_ ()    ← discard $ meas $ q;
    output r.
Lemma alt_UV_WT : forall W (U V : Unitary W), Typed_Box (alt_UV U V).  
Proof. type_check. Qed.

(* Probably want a lemma about alternate's behavior *)
Lemma lift_alternate_eq : forall W (U V : Unitary W), lift_UV U V ≡ alt_UV U V.
Proof.
  intros W U V.
  repeat (autounfold with den_db; intros; simpl).
  simpl.
  rewrite plus_0_r.
  rewrite Nat.sub_0_r.
  rewrite Nat.leb_refl.
  rewrite Nat.sub_diag.
  simpl.
  unfold Splus.
(*  Msimpl.*)
Admitted.  

(** Equality 3: U; meas-discard = meas-discard **)

Definition U_meas_discard (U : Unitary Qubit) := 
  box_ q ⇒ discard $ meas $ U $ q.
Lemma U_meas_discard_WT : forall (U : Unitary Qubit), Typed_Box (U_meas_discard U).  
Proof. type_check. Qed.

Definition meas_discard := 
  box_ q ⇒ discard $ meas $ q.
Lemma meas_discard_WT : Typed_Box meas_discard.  
Proof. type_check. Qed.

Lemma U_meas_eq_meas : forall U, U_meas_discard U ≡ meas_discard.
Proof.
Admitted.
(*
  repeat (autounfold with den_db; intros; simpl).
  specialize (WF_Mixed _ H); intros WFρ.
  specialize (unitary_let_unitary U); intros [WFU UU].
  simpl in *. 
  Msimpl.
  rewrite Mmult_plus_distr_l.
  rewrite Mmult_plus_distr_r.
  solve_matrix.
  specialize (mixed_state_trace_1 _ H); intros trρ.
  unfold trace in trρ. simpl in trρ. rewrite Cplus_0_l in trρ.
  rewrite trρ.
  remember (denote_unitary U) as u.
  repeat rewrite Cmult_plus_distr_r.
  remember (u 0%nat 0%nat) as u00. remember (u 0%nat 1%nat) as u01.
  remember (u 1%nat 0%nat) as u10. remember (u 1%nat 1%nat) as u11.
  remember (ρ 0%nat 0%nat) as ρ00. remember (ρ 0%nat 1%nat) as ρ01.
  remember (ρ 1%nat 0%nat) as ρ10. remember (ρ 1%nat 1%nat) as ρ11.
  repeat rewrite Cplus_assoc.
  repeat rewrite (Cmult_comm _ ρ00), (Cmult_comm _ ρ01), 
                 (Cmult_comm _ ρ10), (Cmult_comm _ ρ11).
  remember (ρ00 * u00 * u00 ^* ) as c000. remember (ρ00 * u10 * u10 ^* ) as c001.
  remember (ρ10 * u01 * u00 ^* ) as c100. remember (ρ10 * u11 * u10 ^* ) as c101.
  remember (ρ01 * u00 * u01 ^* ) as c010. remember (ρ01 * u10 * u11 ^* ) as c011.
  remember (ρ11 * u01 * u01 ^* ) as c110. remember (ρ11 * u11 * u11 ^* ) as c111.
  assert (c000 + c100 + c010 + c110 + c001 + c101 + c011 + c111 = 1).   
  { repeat rewrite <- Cplus_assoc. rewrite (Cplus_comm c110).
    repeat rewrite <- Cplus_assoc. rewrite (Cplus_comm c010).
    repeat rewrite <- Cplus_assoc. rewrite (Cplus_comm c100).
    repeat rewrite Cplus_assoc.
    replace (c000 + c001) with ρ00.
    Focus 2.
      subst.
      repeat rewrite <- Cmult_assoc.
      rewrite <- Cmult_plus_distr_l.
      assert (((denote_unitary U) † × denote_unitary U ) 0 0 = Id 2 0 0)%nat 
        by (rewrite <- UU; reflexivity).
      unfold Mmult, Id, conj_transpose in H0. simpl in H0.
      autorewrite with C_db in H0.
      rewrite Cmult_comm in H0.
      rewrite (Cmult_comm ((denote_unitary U 1%nat 0%nat) ^* )) in H0.
      rewrite H0.                 
      clra.
    rewrite <- 3 Cplus_assoc.
    rewrite (Cplus_assoc c111).
    replace (c111 + c110) with ρ11.
    Focus 2.
      subst.
      repeat rewrite <- Cmult_assoc.
      rewrite <- Cmult_plus_distr_l.
      assert (((denote_unitary U) † × denote_unitary U ) 1 1 = Id 2 1 1)%nat 
        by (rewrite <- UU; reflexivity).
      unfold Mmult, Id, conj_transpose in H0. simpl in H0.
      autorewrite with C_db in H0.
      rewrite Cmult_comm in H0.
      rewrite Cplus_comm in H0.
      rewrite Cmult_comm in H0.
      rewrite H0.                 
      clra.
    rewrite (Cplus_comm ρ11).
    rewrite <- Cplus_assoc.
    repeat rewrite (Cplus_assoc c011).
    replace (c011 + c010) with C0.
    Focus 2.
      subst.
      repeat rewrite <- Cmult_assoc.
      rewrite <- Cmult_plus_distr_l.
      assert (((denote_unitary U) † × denote_unitary U ) 1 0 = Id 2 1 0)%nat 
        by (rewrite <- UU; reflexivity).
      unfold Mmult, Id, conj_transpose in H0. simpl in H0.
      autorewrite with C_db in H0.
      rewrite Cmult_comm in H0.
      rewrite Cplus_comm in H0.
      rewrite Cmult_comm in H0.
      rewrite H0.                 
      clra.
    rewrite Cplus_0_l.
    rewrite <- Cplus_assoc.
    repeat rewrite (Cplus_assoc c101).
    replace (c101 + c100) with C0.
    Focus 2.
      subst.
      repeat rewrite <- Cmult_assoc.
      rewrite <- Cmult_plus_distr_l.
      assert (((denote_unitary U) † × denote_unitary U ) 0 1 = Id 2 0 1)%nat 
        by (rewrite <- UU; reflexivity).
      unfold Mmult, Id, conj_transpose in H0. simpl in H0.
      autorewrite with C_db in H0.
      rewrite Cmult_comm in H0.
      rewrite Cplus_comm in H0.
      rewrite Cmult_comm in H0.
      rewrite H0.                 
      clra.
    rewrite Cplus_0_l.
    assumption.
  } 
  rewrite H0. 
  reflexivity.
Qed.

*) 
       
(** Equality 4: init; meas = new **)


Definition init_meas (b : bool) : Box One Bit := 
  box_ () ⇒ 
    let_ q ← unbox (init b) ();
    let_ b ← meas $ q;
    output b. 
Lemma init_meas_WT : forall b, Typed_Box (init_meas b).
Proof. destruct b; type_check. Qed.

Definition init_meas_new : forall b, init_meas b ≡ new b.
Proof.
  destruct b; simpl.
  - repeat (autounfold with den_db; intros; simpl).
    specialize (WF_Mixed _ H); intros WFρ.
    Msimpl; solve_matrix.
  - repeat (autounfold with den_db; intros; simpl).
    specialize (WF_Mixed _ H); intros WFρ.
    Msimpl; solve_matrix.
Qed.

(** Equality 5: init b; alt b U V = init b; if b then U else V **) 

Definition init_alt {W}  (b : bool) (U V : Unitary W) : Box W (Qubit ⊗ W) := 
  box_ qs ⇒ 
    let_ q   ← init b $ ();
    let_ (q,qs) ← alternate U V $ (q,qs);
    (q,qs).
Lemma init_alt_WT : forall W b (U V : Unitary W), Typed_Box (init_alt b U V).
Proof. type_check. Qed.

Definition init_if {W}  (b : bool) (U V : Unitary W) : Box W (Qubit ⊗ W) := 
  box_ qs ⇒ 
    let_ q   ← unbox (init b) ();
    let_ qs ← (if b then U else V) $ qs;
    (q,qs).
Lemma init_if_WT : forall W b (U V : Unitary W), Typed_Box (init_if b U V).
Proof. type_check. Qed.

Lemma init_alt_if_qubit : forall b (U V : Unitary Qubit), init_alt b U V ≡ init_if b U V.
Proof.
  destruct b; simpl.
  - repeat (autounfold with den_db; intros; simpl).
    specialize (WF_Mixed _ H); intros WFρ.
    specialize (WF_unitary U). simpl; intros WFU.
    specialize (WF_unitary V). simpl; intros WFV.
    Msimpl.
    repeat rewrite <- Mmult_assoc.
    repeat rewrite (Mmult_assoc _ _ _ _ _ swap swap).
    Msimpl.
    solve_matrix.
  - repeat (autounfold with den_db; intros; simpl).
    specialize (WF_Mixed _ H); intros WFρ.
    specialize (WF_unitary U). simpl; intros WFU.
    specialize (WF_unitary V). simpl; intros WFV.
    Msimpl.
    repeat rewrite <- Mmult_assoc.
    repeat rewrite (Mmult_assoc _ _ _ _ _ swap swap).
    Msimpl.
    solve_matrix.
Qed.

Lemma init_alt_if : forall W b (U V : Unitary W), init_alt b U V ≡ init_if b U V.
Proof.
  destruct b; simpl.
  - repeat (autounfold with den_db; intros; simpl).
    specialize (WF_Mixed _ H); intros WFρ.
Admitted.  

(** Equality 6: init b; X b = init ~b **) 

Definition init_X (b : bool) : Box One Qubit :=
  box_ () ⇒ X $ init b $ ().
Lemma init_X_WT : forall b, Typed_Box (init_X b).
Proof. type_check. Qed.

Lemma init_X_init : forall b, init_X b ≡ init (negb b).
Proof.
  destruct b; simpl.
  - repeat (autounfold with den_db; intros; simpl).
    specialize (WF_Mixed _ H); intros WFρ.
    Msimpl.
    repeat rewrite <- Mmult_assoc.
    Msimpl.
    repeat rewrite Mmult_assoc.
    Msimpl.
    reflexivity.    
  - repeat (autounfold with den_db; intros; simpl).
    specialize (WF_Mixed _ H); intros WFρ.
    Msimpl.
    repeat rewrite <- Mmult_assoc.
    Msimpl.
    repeat rewrite Mmult_assoc.
    Msimpl.
    reflexivity.    
Qed.
  
(* Additional Equalities *)



(** Equation 7: lift x <- b; new x = id b **)


Lemma new_WT : forall b, Typed_Box (new b).
Proof. destruct b; type_check. Qed.

Definition lift_new : Box Bit Bit :=
  box_ b ⇒ 
    lift_ x ← b; 
    new x $ ().
Lemma lift_new_WT : Typed_Box lift_new.
Proof. type_check. Qed.

Hint Unfold Splus : den_db.

Definition classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Lemma lift_new_new : forall (ρ : Density 2), Mixed_State ρ -> 
                                        classical ρ -> 
                                        ⟦lift_new⟧ ρ = ⟦@id_circ Bit⟧ ρ.
Proof. 
  intros ρ M C.

simpl.
  repeat (autounfold with den_db; intros; simpl).
  specialize (WF_Mixed _ M); intros WFρ. 
(*  autorewrite with M_db.*)
  Msimpl.
  solve_matrix.
  rewrite C; trivial; omega.
  rewrite C; trivial; omega.
Qed.  


(** Equation 7': meas q; lift x <- p; new x = meas q **)

Definition meas_lift_new : Box Qubit Bit :=
  box_ q ⇒ 
    let_ b ← meas $ q;
    lift_ x ← b; 
    new x $ ().
Lemma meas_lift_new_WT : Typed_Box meas_lift_new.
Proof. type_check. Qed.

Lemma meas_lift_new_new : meas_lift_new ≡ boxed_gate meas.
Proof. 
  intros ρ safe M.
  repeat (autounfold with den_db; intros; simpl).
  specialize (WF_Mixed _ M); intros WFρ.
  Msimpl.
  solve_matrix.
Qed.
  