Require Import Contexts.
Require Import FlatCircuits.
Require Import TypedCircuits.
Require Import Program.

(* No input, output length 
Inductive Machine_Circuit : Set :=
| m_output : Machine_Circuit
| m_gate   : forall (l : list nat) {w1 w2}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit
             -> Machine_Circuit.
*)

(* Version with output length.
Inductive Machine_Circuit : list nat -> Set :=
| m_output : forall l, Machine_Circuit l
| m_gate   : forall {l l' : list nat} {w1 w2}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit l'
             -> Machine_Circuit l'.
*)

Require Import Denotation.
Require Import List.
About make_env.

Inductive Machine_Circuit : nat -> Set :=
| m_output : forall (l : list nat), Machine_Circuit (length l)
| m_gate   : forall (l : list nat) {w1 w2 n}, 
               length l = (〚w1〛)
             -> Gate w1 w2
             -> Machine_Circuit n
             -> Machine_Circuit n.

(* morally, a Machine_Box m n should only use variables less than m*)
Inductive Machine_Box : nat -> nat -> Set := 
| m_box : forall m {n}, Machine_Circuit n -> Machine_Box m n.

(* Naivest possible composition: 
  only makes sense for circuits without input/output
Fixpoint m_compose (c1 c2 : Machine_Circuit) : Machine_Circuit :=
  match c1 with
  | m_output => c2
  | m_gate l eq g c1' => m_gate l eq g (m_compose c1' c2)
  end.
*)

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


(* This is similar to make_env from Denotation. *)

Definition Machine_List n := {ls : list nat | length ls = n}.

(*
Definition ml_interleave {Γ1 Γ2 : OCtx} (disj : is_valid (Γ1 ⋓ Γ2))
                         (ls1 : Machine_List (〚Γ1〛)) (ls2 : Machine_List (〚Γ2〛)) :
                         Machine_List (〚Γ1 ⋓ Γ2〛).
Proof.
  destruct Γ1 as [ | Γ1]; [exists []; auto | ].
  destruct Γ2 as [ | Γ2]; [exists []; auto | ].
  destruct ls1 as [ls1 pf1].
  destruct ls2 as [ls2 pf2].
  revert ls1 ls2 pf1 pf2.
  apply valid_disjoint in disj.
  inversion disj; subst; clear disj; rename H1 into disj.
  induction disj; intros ls1 ls2 pf1 pf2.
  - rewrite merge_nil_l; exists ls2; auto.
  - rewrite merge_nil_r; exists ls1; auto.
  - apply disjoint_valid in disj. destruct (Γ1 ⋓ Γ2) as [ | Γ] eqn:pf;
    [ absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite pf. simpl. apply (IHdisj ls1 ls2); auto.
  - apply disjoint_valid in disj. destruct (Γ1 ⋓ Γ2) as [ | Γ] eqn:pf;
    [ absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite pf. simpl. destruct ls1 as [ | n ls1]; [inversion pf1 | ].
    destruct (IHdisj ls1 ls2) as [IH_ls IH_pf]; auto.
    exists (n :: IH_ls); simpl; auto.
  - apply disjoint_valid in disj. destruct (Γ1 ⋓ Γ2) as [ | Γ] eqn:pf;
    [ absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite pf. simpl. destruct ls2 as [ | n ls2]; [inversion pf2 | ].
    destruct (IHdisj ls1 ls2) as [IH_ls IH_pf]; auto.
    exists (n :: IH_ls); simpl; auto.
Defined.


Program Definition ml_shift {n} m : Machine_List n -> Machine_List n :=
  map (fun i => m + i).
Next Obligation.
  destruct x as [ls pf].
  simpl. rewrite map_length. auto.
Defined.


Program Definition ml_merge (Γ1 Γ2 : OCtx)
                             (ls1 : Machine_List (〚Γ1〛)) (ls2 : Machine_List (〚Γ2〛)) 
                            : Machine_List (〚Γ1 ⋓ Γ2〛) :=
  match merge_dec Γ1 Γ2 with
  | inleft disj => let ls2' := ml_shift (〚Γ1〛) ls2 in
                   ml_interleave disj ls1 ls2
  | inright _   => []
  end.
Next Obligation.
  rewrite wildcard'. auto.
Defined.
*)

Fixpoint pat_to_list {Γ W} (p : Pat Γ W) : list nat :=
  match p with
  | pair Γ1 Γ2 Γ0 W1 W2 valid merge p1 p2 => 
      let ls1 := pat_to_list p1 in
      let ls2 := pat_to_list p2 in 
      ls1 ++ ls2
  | qubit x Γ sing => [x]
  | bit   x Γ sing => [x]
  | unit => []
  end.
Lemma pat_to_list_length : forall Γ W (p : Pat Γ W), length (pat_to_list p) = 〚W〛.
Admitted.


Print Gate.
Require Import PeanoNat.

Fixpoint subst_eq_length (ls1 ls2 : list nat) : nat -> nat :=
  match ls1, ls2 with
  | m1 :: ls1, m2 :: ls2 => fun i => if Nat.eq_dec i m2 then m1 else (subst_eq_length ls1 ls2) i
  | _, _ => id
  end.

Definition subst_add (bound : nat) (ls2 : list nat) : nat * (nat -> nat) :=
  let new_bound := bound + length ls2 in
  (new_bound, subst_eq_length (seq bound (length ls2)) ls2).

Definition subst_add_1 (bound : nat) (ls2 : list nat) : nat -> nat :=
  match ls2 with
  | [m2] => fun i => if Nat.eq_dec i m2 then bound else i
  | _    => id
  end.

Definition subst_remove_1 (ls1 : list nat) : nat -> nat :=
  match ls1 with
  | [m1] => fun i => if Nat.ltb m1 i then i-1 else i
  | _    => id
  end.
  
(* Returns a new bound and a substitution *)
Definition subst_with_gate {W1 W2} (bound : nat) (g : Gate W1 W2) (p1 p2 : list nat) 
                           : nat -> nat :=
  match g with
  | U W u   => subst_eq_length p1 p2
  | meas    => subst_eq_length p1 p2
  | init0   => subst_add_1 bound p2
  | init1   => subst_add_1 bound p2
  | new0    => subst_add_1 bound p2
  | new1    => subst_add_1 bound p2
  | discard => subst_remove_1 p1
  end.
Print Machine_Circuit.

Definition apply_substitution {n} (f : nat -> nat) (C : Machine_Circuit n) : Machine_Circuit n.
Proof.
  induction C.
  - set (c' := m_output (map f l)). rewrite map_length in c'. exact c'.
  - assert (e' : length (map f l) = 〚w1〛). { rewrite map_length. exact e. }
    apply (m_gate (map f l) e' g IHC).
Defined.

Program Fixpoint Flat_to_Machine_Circuit {Γ W} (C : Flat_Circuit Γ W)  
                 : Machine_Circuit (〚W〛) :=
  match C with
  | flat_output Γ Γ' W eq p => m_output (pat_to_list p)
  | flat_gate Γ Γ1 Γ1' Γ2 Γ2' W1 W2 W v1 v2 m1 m2 g p1 p2 C' => 
    let ls1 := pat_to_list p1 in
    let ls2 := pat_to_list p2 in
    let f := subst_with_gate (〚Γ ⋓ Γ1〛) g ls1 ls2 in
    m_gate (pat_to_list p1) _ g (apply_substitution f (Flat_to_Machine_Circuit C'))
  | flat_lift Γ1 Γ2 Γ W W' v m p f => _
  end.
Next Obligation. apply pat_to_list_length. Defined.
Next Obligation. apply pat_to_list_length. Defined.
Next Obligation. (* No correspondence for lift *) Admitted.






(* *)