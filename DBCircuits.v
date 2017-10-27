Require Import Contexts.
Require Import HOASCircuits.
Require Import Program.
Require Import List.
Require Import Monad.
Import Arith.
Open Scope circ_scope.

(* A minimal circuit *)
(* A well-formed DeBruijn_Circuit n w has exactly n input wires. 
*)
Inductive DeBruijn_Circuit (*n : nat*) (w : WType) : Set :=
| db_output : (*forall {pf : n = size_WType w},*) Pat w -> DeBruijn_Circuit w
| db_gate   : forall {w1 w2} (*{pf : n + size_WType w2 = n' + size_WType w1}*),
               Gate w1 w2 -> Pat w1 -> DeBruijn_Circuit w -> DeBruijn_Circuit w
| db_lift   :  (*{pf : n = S n'}*)
               Pat Bit -> (bool -> DeBruijn_Circuit w) -> DeBruijn_Circuit w
.

Inductive DeBruijn_Box (w1 w2 : WType) : Set :=
| min_box : DeBruijn_Circuit w2 -> DeBruijn_Box w1 w2.

Arguments db_output {w}.
Arguments db_gate {w w1 w2 }.
Arguments db_lift {w}.


(* Throughout this development, we will want to update some state based on the
presence of a gate. This is handled by a type class Gate_State, which models how
a gate might affect some underlying state:

    - We might need to create a fresh variable;

    - We might need to remove a variable from the state;

    - We might need to change the type of a variable in the state. Not all
      states will keep track of the type, but some will.
*)
Class Gate_State A :=
  { get_fresh  : WType -> State A Var 
  ; remove_var : Var -> A -> A
  ; change_type : Var -> WType -> A -> A
  }.

(* process_gate_pat g p a returns the pattern that is obtained from running the
   gate g with input pattern p and state a 
*)
Definition process_gate_pat {A w1 w2} `{Gate_State A} (g : Gate w1 w2) : Pat w1 -> A -> Pat w2 :=
  match g with 
  | U _           => fun p _ => p
  | init0 | init1 => fun _ a => qubit (fst (get_fresh Qubit a))
  | new0 | new1   => fun _ a => bit (fst (get_fresh Bit a))
  | meas          => fun p _ => match p with
                                | qubit x => bit x
                                end
  | discard       => fun _ _ => unit
  end.

(* process_gate_state g p a returns the state that is obtained from running the
   gate g with input pattern p and state a. The two functions process_gate_pat
   and process_gate_state could be combined into one operation in a state monad,
   but the result requires a lot of bulky infrastructure for dealing with
   monads, unfortunately. It may be easier just to take two passes over the gate.
*)
Definition process_gate_state {A w1 w2} `{Gate_State A} (g : Gate w1 w2) : Pat w1 -> A -> A :=
  match g with 
  | U _           => fun _ a => a
  | init0 | init1 => fun _ a => snd (get_fresh Qubit a)
  | new0 | new1   => fun _ a => snd (get_fresh Bit a)
  | meas          => fun p a => match p with
                                | qubit x => change_type x Bit a
                                end
  | discard       => fun p a => match p with
                                | bit x => remove_var x a
                                end
  end.


(**********************)  
(* De Bruijn Contexts *)
(**********************)

Definition DB_Ctx := list WType.
Definition DB_to_Ctx (Γ : DB_Ctx) : Ctx := fmap Some Γ.

Fixpoint remove_at  {A} (i : nat) (ls : list A) :=
  match i, ls with
  | _   ,[]        => []
  | 0   , _ :: ls' => ls'
  | S i', a :: ls' => a :: remove_at i' ls'
  end.
Fixpoint update_at {A} (ls : list A) (i : nat) (a : A) : list A :=
  match ls, i with
  | []      , _    => []
  | _ :: ls', 0    => a :: ls'
  | b :: ls', S i' => b :: update_at ls' i' a
  end.


Instance DB_Ctx_State : Gate_State DB_Ctx :=
  { get_fresh w  := do Γ ← get;
                    do _ ← put (w :: Γ);
                    return_ 0
  ; remove_var := remove_at
  ; change_type x w Γ := update_at Γ x w
  }.


(**********)
(* Typing *)
(**********)

Definition Types_DB_Pat {w} (Γ : DB_Ctx) (p : Pat w) := Types_Pat (DB_to_Ctx Γ) p.

(* Although we use ordinary (nominal) contexts for typing, it should be the case
that they are always "minimal", meaning that the list is equivalent to a list of
WTypes (as opposed to list (option WType)). However, because of context
splitting, this will only be enforcable at the top level. *)
Inductive Types_DB {w} (Γ : DB_Ctx) : DeBruijn_Circuit w -> Prop :=
| types_db_output : forall p, Types_DB_Pat Γ p -> Types_DB Γ (db_output p)
| types_db_gate   : forall Γ1 Γ2 w1 w2 (g : Gate w1 w2) p c,
                    Γ = Γ1 ++ Γ2 ->
                    Types_DB_Pat Γ1 p ->
                    Types_DB ((process_gate_state g p Γ1) ++ Γ2 ) c ->
                    Types_DB Γ (db_gate g p c)
| types_db_lift   : forall Γ1 Γ2 p f,
                    Γ = Γ1 ++ Γ2 ->
                    Types_DB_Pat Γ1 p ->
                    (forall b, Types_DB Γ2 (f b)) ->
                    Types_DB Γ (db_lift p f)
.

(*****************)
(* Substitutions *)
(*****************)

(* A substitution σ is a finite map from a variable x to a natural number i,
   where σ[i]=x. 
   This formulation of finite maps is unique because when a variable is removed from the list, 
   all variables above that one are shifted downward. 
*)
Definition substitution := list Var.

Print Gate_State.
Record subst_state := Mk_subst_state
  { get_σ : substitution
  ; fresh : nat }. 

Instance substitution_Gate_State : Gate_State subst_state :=
  { get_fresh w st := let x := fresh st in 
                      (x, Mk_subst_state (x :: get_σ st) (S x))
  ; remove_var x st := let σ' := List.remove Nat.eq_dec x (get_σ st) in
                        Mk_subst_state σ' (fresh st)
  ; change_type x w st := st
  }.
                      

Fixpoint mk_subst {w} (p : Pat w) : substitution :=
  match p with
  | unit       => []
  | bit x      => [x]
  | qubit x    => [x]
  | pair p1 p2 => (mk_subst p1) ++ (mk_subst p2)
  end.
Definition mk_subst_state {w} (p : Pat w) : subst_state :=
  let σ := mk_subst p in
  Mk_subst_state σ (fold_left max σ 0).


Definition remove_pat {A} `{Gate_State A} {w} (p : Pat w) (a : A) : A :=
  fold_left (fun a x => remove_var x a)  (mk_subst p) a.


(* Precondition: x must appear in li *)
Fixpoint lookup (x : Var) (li : list Var) : nat :=
  match li with
  | nil => 0
  | y :: ys => if x =? y then 0 else S (lookup x ys)
  end.
Fixpoint index {A} (i : nat) (li : list A) : option A :=
  match i, li with
  | _, nil => None
  | 0, x :: _ => Some x
  | S i', _ :: li' => index i' li'
  end.

Definition subst_var (σ : substitution) (x : Var) := lookup x σ.
Fixpoint subst_pat (σ : subst_state) {w} (p : Pat w) : Pat w :=
  match p with
  | unit    => unit
  | qubit x => qubit (subst_var (get_σ σ) x)
  | bit   x => bit (subst_var (get_σ σ) x)
  | pair p1 p2 => pair (subst_pat σ p1) (subst_pat σ p2)
  end.

Fixpoint subst_db (σ : subst_state) {w} (c : DeBruijn_Circuit w) 
                : DeBruijn_Circuit w :=
  match c with
  | db_output p    => db_output (subst_pat σ p)
  | db_gate g p c' => let p' := subst_pat σ p in
                      let σ' := process_gate_state g p σ in
                      db_gate g p' (subst_db σ' c')
  | db_lift p f    => let p' := subst_pat σ p in
                      let σ' := remove_pat p σ in
                      db_lift p' (fun b => subst_db σ' (f b))
  end.

About index. About lookup.
(* starting at i=|Γ|-1, finds the x such that x ↦ i ∈ σ, then looks up the type W of
   x in Γ. Adds the binding W to the head of the resulting DB_Ctx; by the end
   the process, this binding will be at index i in the list. *)
Fixpoint subst_ctx' (Γ : DB_Ctx) (σ : substitution) (i : nat) : option DB_Ctx :=
  match i with
  | 0   => return_ []
  | S j => do x  ← index j σ;
           do W  ← index x Γ;
           do Γ' ← subst_ctx' Γ σ j;
           return_ (W :: Γ')
  end.
Definition subst_ctx (Γ : DB_Ctx) (σ : substitution) : DB_Ctx :=
  match subst_ctx' Γ σ (length Γ) with
  | Some Γ' => Γ'
  | None => []
  end.

(*
Definition Types_subst (Γ : DB_Ctx) (σ : substitution) (Γ' : DB_Ctx) :=
  forall x x', lookup x σ = x' ->
               (forall w, index x Γ = Some w <-> index x' Γ' = Some w).

Lemma types_subst_length : forall Γ σ Γ',
      Types_subst Γ σ Γ' -> length Γ = length Γ'.
Proof.
  induction Γ; intros σ Γ' pf.
Admitted (* this will take some work, but it should be true *).
*)
  

Lemma singleton_index : forall x w Γ,
      SingletonCtx x w (DB_to_Ctx Γ) <-> ((index x Γ = Some w) * (length Γ = 1)).
Proof.
  induction x; intros.
  - destruct Γ.
    * split; simpl.
      + inversion 1. 
      + destruct 1 as [H _]; inversion H.
    * split; simpl; intros H.
      + inversion H; subst.
        destruct Γ; [ | inversion H3].
        split; auto.
      + destruct H as [H1 H2].
        inversion H1; subst.
        destruct Γ; [ | inversion H2].
        constructor.
  - split; [intros H | intros [H1 H2]].
    + inversion H. destruct Γ; inversion H1.
    + destruct Γ; [inversion H2 | ]. 
      simpl in *.
      destruct Γ; [ | inversion H2].
      destruct x; inversion H1.
Qed.


(* A well-formed (linear) substitution on debruijn indices is an isomorphism on
   the set [1..n] *) 
Require Import Permutation.
(*Definition subst_iso (σ : substitution) :=
  Permutation σ (seq 0 (length σ - 1)).*)

Definition WF_subst (Γ : DB_Ctx) σ : Prop := Permutation σ (seq 0 (length Γ)).

Lemma wf_subst_length : forall Γ σ, WF_subst Γ σ -> length Γ = length σ.
Admitted.

Lemma subst_ctx_nil : forall σ,
      subst_ctx [] σ = [].
Proof. 
  intros.
  unfold subst_ctx.
  reflexivity.
Qed.


Lemma singleton_db_ctx : forall x w Γ,
      SingletonCtx x w (DB_to_Ctx Γ) <->
      x = 0 /\ Γ = [w].
Proof.
  intros. split.
  * destruct Γ as [ | y [ | z Γ' ]]; intros pf_singleton; simpl in *.
    - inversion pf_singleton.
    - inversion pf_singleton. auto.
    - inversion pf_singleton.
  * intros H; destruct H; subst.
    unfold DB_to_Ctx.
    simpl.
    constructor.
Qed.


Lemma wf_subst_lookup_0 : forall σ w,
      WF_subst [w] σ ->
      lookup 0 σ = 0.
Admitted.

  
Lemma subst_ctx_singleton : forall w σ,
      WF_subst [w] σ -> 
      subst_ctx [w] σ = [w].
Proof. 
  intros.
  assert (length σ = 1).
  { erewrite <- wf_subst_length; eauto. auto.
  }
    destruct σ as [ | i [ |  ]]; inversion H0.
    assert (i = 0).
    { unfold WF_subst in H. simpl in H.
      apply Permutation_length_1; auto.
    }
  subst.
  unfold subst_ctx.
  reflexivity.
Qed.
(*
Lemma wf_subst_merge : 
      WF_subt Γ σ ->
      Γ = Γ1 ⋓ Γ2 -> 
*)
Lemma types_subst_pat_db : forall w (p : Pat w) Γ Γ' σ ,
      Γ' = subst_ctx Γ (get_σ σ) ->
      WF_subst Γ (get_σ σ) ->
      Types_DB_Pat Γ p ->
      Types_DB_Pat Γ' (subst_pat σ p).
Proof.
  induction p; intros Γ Γ' σ types_σ σ_iso types_p; simpl.
  - assert (Γ = []) by (destruct Γ; auto; inversion types_p). subst.
    rewrite subst_ctx_nil. constructor.
  - unfold subst_var. inversion types_p. subst.

    apply singleton_db_ctx in H1.
    destruct H1; subst.

    assert ( H : lookup 0 (get_σ σ) = 0).
    { eapply wf_subst_lookup_0; eauto.
    }
    rewrite H.
    rewrite subst_ctx_singleton; auto.
  - unfold subst_var. inversion types_p. subst.

    apply singleton_db_ctx in H1.
    destruct H1; subst.

    assert ( H : lookup 0 (get_σ σ) = 0).
    { eapply wf_subst_lookup_0; eauto.
    }
    rewrite H.
    rewrite subst_ctx_singleton; auto.
  - unfold Types_DB_Pat in types_p.
    dependent destruction types_p. 
    admit (* need facts about mergine with DB_Ctx's *).

Admitted.


  

Lemma types_subst_db : forall w (c : DeBruijn_Circuit w) Γ ,
      Types_DB Γ c ->
      forall {σ Γ'},
      Γ' = subst_ctx Γ (get_σ σ) ->
      WF_subst Γ (get_σ σ) ->
      Types_DB Γ' (subst_db σ c).
Proof.
  induction 1; intros σ Γ' pf_Γ' types_σ; simpl.
  - constructor.
    eapply types_subst_pat_db; eauto.
  - econstructor; eauto.
    * admit (* requires an extra lemma about merging and substituting *).
    * eapply types_subst_pat_db; [ reflexivity | | eauto]. 
      admit. (* redefined WF_subst *)
    * apply IHTypes_DB.
      + admit (* lemma *).
      + admit (* lemma *).
  - econstructor. admit. 
    eapply types_subst_pat_db; [ reflexivity | | eauto ]. admit.
    intros b. apply H2. reflexivity. admit.
Admitted.
    
      
             
    


(***************)
(* composition *)
(***************)


Fixpoint db_compose {w w'} (c : DeBruijn_Circuit w) (c' : DeBruijn_Circuit w') 
                  : DeBruijn_Circuit w' :=
  match c with
  | db_output p   => subst_db (mk_subst_state p) c'
  | db_gate g p c => db_gate g p (db_compose c c')
  | db_lift p f   => db_lift p (fun b => db_compose (f b) c')
  end.

Fixpoint WType_to_DB_Ctx w :=
  match w with
  | One => []
  | Qubit => [Qubit] 
  | Bit => [Bit] 
  | W1 ⊗ W2 => WType_to_DB_Ctx W1 ++ WType_to_DB_Ctx W2
  end.

Lemma db_compose_correct : forall {w Γ1} (c : DeBruijn_Circuit w), Types_DB Γ1 c ->
                           forall {w' Γ2 Γ} (c' : DeBruijn_Circuit w'),
    Γ2 = WType_to_DB_Ctx w ->
    Types_DB (Γ2 ++ Γ) c' -> Types_DB (Γ1 ++ Γ) (db_compose c c').
Proof.
  induction 1; intros w' Γ02 Γ0 c' H_Γ types_c'.
  - simpl. subst.
    eapply types_subst_db; eauto.
    admit.
    admit.
  - simpl.
    econstructor; [ | eauto | ]. admit.
    admit (* IH here *).
  - simpl.
    econstructor; [ | eauto | ]. admit. intros.
    eapply H2; [ | apply types_c'].
    admit.
Admitted.
  