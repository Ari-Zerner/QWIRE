Require Import Datatypes.
Require Export TypeChecking.
Import ListNotations.
Open Scope list_scope.
Open Scope circ_scope.

Definition apply_box {w1 w2} (b : Box w1 w2) (c : Circuit w1) : Circuit w2 :=
  let_ x ← c;
  unbox b x.
Notation "b $ c" := (apply_box b c)  (right associativity, at level 10) : circ_scope.
Coercion output : Pat >-> Circuit.

Lemma apply_box_WT : forall σ τ (b : Box σ τ) (c : Circuit σ) Δ,
      is_valid Δ ->
      Typed_Box b -> Δ ⊢ c :Circ -> Δ ⊢ b $ c :Circ.
Proof.
  intros σ τ b c Δ pf_Δ pf_b pf_c.
  eapply compose_typing.
  - eauto.
  - type_check. apply pf_b. type_check.
  - type_check.
Qed.
 


Theorem box_WT : forall σ₁ σ₂ (f : Pat σ₁ -> Circuit σ₂),
                 Typed_Box (box f) ->
                 forall Δ (p : Pat σ₁), 
                 Δ ⊢ p :Pat -> Δ ⊢ f p :Circ.
Proof.


Definition id_circ {W} : Box W W :=
  box_ p ⇒ (output p).
Lemma id_circ_WT : forall W, Typed_Box (@id_circ W).
Proof. type_check. Qed.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Box W1 W2 := 
  box_ p ⇒ 
    gate_ p2 ← g @ p;
    output p2.
Lemma boxed_gate_WT {W1 W2} (g : Gate W1 W2) : Typed_Box (boxed_gate g).
Proof. type_check. Qed.
Coercion boxed_gate : Gate >-> Box.

Definition SWAP : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) := 
  box_ p ⇒ let_ (p1,p2) ← p; (p2,p1).
Lemma WT_SWAP : Typed_Box SWAP. Proof. type_check. Qed.


(***********************)
(* Structural circuits *)
(***********************)

Definition init (b : bool) : Box One Qubit :=
  if b then init1 else init0.
Lemma init_WT : forall b, Typed_Box (init b).
Proof. destruct b; type_check. Defined.

Definition assert (b : bool) : Box Qubit One := if b then assert1 else assert0.
Lemma assert_WT : forall b, Typed_Box (assert b). Proof. type_check. Qed.

Definition inSeq {w1 w2 w3} (c1 : Box w1 w2) (c2 : Box w2 w3): Box w1 w3 :=
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.

Lemma inSeq_WT : forall W1 W2 W3 (c1 : Box W1 W2) (c2 : Box W2 W3), 
                 Typed_Box c1 -> Typed_Box c2 -> Typed_Box (inSeq c1 c2).
Proof. type_check. Qed.

Definition inPar {w1 w2 w1' w2'} 
                 (c1 : Box w1 w2) (c2 : Box w1' w2') : Box (w1 ⊗ w1') (w2 ⊗ w2'):=
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    (p1',p2').

Lemma inPar_WT : forall W1 W1' W2 W2' (c1 : Box W1 W2) (c2 : Box W1' W2'), 
  Typed_Box c1 -> Typed_Box c2 ->
  Typed_Box (inPar c1 c2).
Proof. type_check. Qed.

Fixpoint units (n : nat) : Pat (n ⨂ One) := 
  match n with
  | O => unit
  | S n' => pair unit (units n')
  end. 
Lemma types_units : forall n, Types_Pat ∅ (units n).
Proof. induction n; type_check. Qed.

(* Can also just use (init b) #n $ (()) *)
Fixpoint initMany (b : bool) (n : nat) : Box One (n ⨂ Qubit):= 
  match n with 
  | 0    => id_circ
  | S n' => box_ () ⇒ 
           let_ q  ← unbox (init b) ();
           let_ qs ← unbox (initMany b n') ();
           (q, qs)
  end.
Lemma initMany_WT : forall b n, Typed_Box (initMany b n).
Proof. induction n; type_check. Qed.

Fixpoint inSeqMany (n : nat) {W} (c : Box W W) : Box W W:= 
  match n with
  | 0 => id_circ
  | S n' => inSeq c (inSeqMany n' c)
  end.
Lemma inSeqMany_WT : forall n W (c : Box W W), 
      Typed_Box c -> Typed_Box (inSeqMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.

Fixpoint inParMany (n : nat) {W W'} (c : Box W W') : Box (n ⨂ W) (n ⨂ W') := 
  match n with 
  | 0    => id_circ
  | S n' => inPar c (inParMany n' c)
  end.
Lemma inParMany_WT : forall n W W' (c : Box W W'), Typed_Box c  -> 
                                 Typed_Box (inParMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.       

(* Parallel binds more closely than sequence *)
Notation "b1 ∥ b2" := (inPar b1 b2) (at level 52, right associativity) : circ_scope.
Notation "b' · b" := (inSeq b b') (at level 60, right associativity) : circ_scope.
Notation "c1 ;; c2" := (inSeq c1 c2) (at level 60, right associativity) : circ_scope.

Notation "(())" := (units _) (at level 0) : circ_scope.
Notation "g # n" := (inParMany n g) (at level 40) : circ_scope.

Hint Resolve types_units id_circ_WT boxed_gate_WT init_WT inSeq_WT inPar_WT 
     initMany_WT inSeqMany_WT inParMany_WT : typed_db.

(*********************)
(** Classical Gates **)
(*********************)

(* These can't be used in oracles since they're not reversible. *)

(* NOT already exists *)

Definition CL_AND : Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒
    let_ (a,b)      ← output ab;
    let_ z         ← init0 $ ();
    let_ (a,(b,z)) ← CCNOT $ (a,(b,z));
    let_ a         ← meas $ a;
    let_ b         ← meas $ b;
    let_ ()        ← discard $ a;   
    let_ ()        ← discard $ b;   
    z.
Lemma CL_AND_WT : Typed_Box CL_AND.
Proof. type_check. Qed.

Definition CL_XOR : Box (Qubit ⊗ Qubit) Qubit := 
  box_ (a,b) ⇒ 
    let_ (a, b) ← CNOT $ (a,b);
    let_ a      ← meas $ a;
    let_ ()     ← discard $ a;
    b.
Lemma CL_XOR_WT : Typed_Box CL_XOR.
Proof. type_check. Qed.

Definition CL_OR : Box (Qubit ⊗ Qubit) Qubit :=
  box_ (a,b) ⇒ 
    let_ a'         ← X $a;
    let_ b'         ← X $b;
    let_ z          ← CL_AND $ (a',b');
    X $z.
Lemma CL_OR_WT : Typed_Box CL_OR.
Proof. type_check. Qed.


(***********************)
(** Reversible Gates  **)
(***********************)

(* Apply the f(x,z) = g(x) ⊕ z construction, where g is the classical function 
   and z is an extra target qubit *)

(* This has a more efficient construction where we simply negate z
Definition TRUE : Box Qubit Qubit :=
  box_ z ⇒ 
    let_ x     ← init1 $();
    let_ (x,z) ← CNOT $(x,z);
    let_ ()    ← assert1 $x;
    output z.
*)
Definition TRUE : Box Qubit Qubit := X.
Lemma TRUE_WT : Typed_Box TRUE.
Proof. type_check. Qed.

(* This has a more efficient construction: the identity
Definition FALSE : Box Qubit Qubit :=
  box_ z ⇒ 
    let_ x     ← init0 $();
    let_ (x,z) ← CNOT $(x,z);
    let_ ()    ← assert0 $x;
    output z.
*)
Definition FALSE : Box Qubit Qubit := id_circ.
Lemma FALSE_WT : Typed_Box FALSE.
Proof. type_check. Qed.

Definition NOT : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x,z) ⇒ 
    let_ x         ← X $x;
    let_ (x,z)     ← CNOT $(x,z);
    let_ x         ← X $x;
    (x,z).
Lemma NOT_WT : Typed_Box NOT.
Proof. type_check. Qed.

Definition AND : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) :=
  box_ xyz ⇒
    let_ (x,y,z)    ← output xyz;
    let_ (x,(y,z)) ← CCNOT $(x,(y,z));
    (x,y,z).    
Lemma AND_WT : Typed_Box AND.
Proof. type_check. Qed.

Definition XOR : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) := 
  box_ xyz ⇒
    let_ (x,y,z)    ← output xyz;
    let_ (x,z)     ← CNOT $(x,z);
    let_ (y,z)     ← CNOT $(y,z);
    (x,y,z).
Lemma XOR_WT : Typed_Box XOR.
Proof. type_check. Qed.

