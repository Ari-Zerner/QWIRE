Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import HOASCircuits.
Require Import FlatCircuits.
(* Import TC. *)
Import ListNotations.
Open Scope list_scope.

(** Projecting out elements of tensors **)

Inductive sigT23 (A:Type) (P Q R : A -> A -> Type) : Type :=
    existT23 : forall (x y : A), P x y -> Q x y -> R x y -> sigT23 A P Q R.

Arguments existT23 {A} {P Q R} x y p1 p2 M.

Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  sigT23 OCtx (fun x y => Pat x W1) (fun x y => Pat y W2) (fun x y => Γ = x ⋓ y) :=
  match p with 
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 v M p1 p2 => existT23 Γ1 Γ2 p1 p2 M  
  end.
(*
Program Definition elim_unit {Γ} (p : Pat Γ One) : Γ = ∅ :=
  match p with
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 v M p1 p2 => _
  end.
*)

(* Examples below use fresh_pat, but I'd rather have concrete patterns *)
(*
Fixpoint concrete_bit (Γ : Ctx) : Ctx :=
  match Γ with
  | nil => [Some Bit]
  | None :: Γ' => Some Bit :: Γ'
  | Some w :: Γ' => Some w :: concrete_bit Γ'
  end.

Fixpoint concrete_qubit (Γ : Ctx) : Ctx :=
  match Γ with
  | nil => [Some Qubit]
  | None :: Γ' => Some Qubit :: Γ'
  | Some w :: Γ' => Some w :: concrete_qubit Γ'
  end.

Fixpoint concrete_tensor (Γ : Ctx) : Ctx
*)

(*** Typechecking Tactic ***)

Open Scope circ_scope.
Opaque wproj.


(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.

Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac type_check_once := 
  intros;
  repeat match goal with 
  | [ p : Pat _ One |- _ ]         => inversion p; subst; clear p
  | [ H : Disjoint ?Γ1 ?Γ2 |- _ ]  => apply disjoint_valid in H; trivial
  end; 
  compute in *; 
  subst; 
  (* Runs monoid iff a single evar appears in context *)
  match goal with 
  | [|- is_valid ?Γ] => tryif (has_evar Γ)   
                        then (idtac (*"can't validate"; print_goal*))
                        else (idtac (*"validate"; print_goal*); validate)
  | [|- ?G ]         => tryif (has_evars G)  
                        then (idtac (*"can't monoid"; print_goal*))
                        else (idtac (*"monoid"; print_goal*); monoid)
  end.

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac "done".

(* Easiest solution *)

Ltac type_check := let n := numgoals in do n [> type_check_once..].

(*** Paper Examples ***)

Set Printing Coercions.

Tactic Notation (at level 0) "make_circ" uconstr(C) := refine C; type_check.
Tactic Notation (at level 0) "box" uconstr(p) uconstr(C) := 
  refine (flat_box p C); type_check.

Ltac new_pat p W Γ v := 
    let Γ' := fresh "Γ" in
    let v' := fresh "v" in
    let v'' := fresh "v" in
(*    let Eq := fresh "Eq" in *)
    destruct (fresh_pat Γ W v) as [Γ' [[v' v''] p]];
    apply disjoint_valid in v''; trivial; try apply valid_empty.

Notation gate g p1 p2 C := (flat_gate _ _ _ _ _ g p1 p2 C).
Notation output p := (flat_output _ p).


Notation "p' ← 'gate' g 'on' p ; C" := (gate g p p' C) 
                                          (at level 10, right associativity). 

Notation "'letC' p' ← 'gate' g 'on' p ; C" := (gate g p p' C) 
                                          (at level 10, right associativity).   


Notation "()" := unit : circ_scope.
Notation "( x , y , .. , z )" := (pair _ _ _ _ _ _ _ .. (pair _ _ _ _ _ _ _ x y) .. z) (at level 0) : circ_scope.


(*

Notation output p := (output _ p).
Notation gate g p1 := (gate _ _ _ g p1 (fun _ _ _ _ p' => output p')).
Notation comp p c1 c2 := (compose c1 _ _ (fun _ _ _ _ p => c2)).
Notation letpair p1 p2 p c := (let 'existT23 _ _ p1 p2 _ := wproj p in c).


Notation "'letC' p ← c1 ; c2" := (comp p c1 c2)
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( p1 , p2 ) ← c1 ; c2" := (compose c1 _ _ (fun _ _ _ _ x => letpair p1 p2 x c2)) 
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( p1 , p2 , p3 ) ← c1 ; c2" :=
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                                      let 'existT23 _ _ p1 p2 _ := wproj y in
                                      c2))
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( ( p1 , p2 ) , p3 ) ← c1 ; c2" := 
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                                      let 'existT23 _ _ p1 p2 _ := wproj y in
                                      c2))
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( p1 , ( p2 , p3 ) ) ← c1 ; c2" :=
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ p1 y  _ := wproj x in
                                      let 'existT23 _ _ p2 p3 _ := wproj y in
                                      c2))
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← c1 ; c2" :=
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ y  z  _ := wproj x in
                                      let 'existT23 _ _ p1 p2 _ := wproj y in
                                      let 'existT23 _ _ p3 p4 _ := wproj z in
                                      c2))
                            (at level 10, right associativity) : circ_scope.


Notation unbox c p := (unbox c _ p).

Notation lift_compose x c1 c2 := (compose c1 _ _ (fun _ _ _ _ p' => lift _ _ p' (fun x => c2))).
Notation lift_pat x p c := (lift _ _ p (fun x => c)).
Notation "'lift' x ← c1 ; c2" := (lift_pat x c1 c2) (at level 10, right associativity) : circ_scope.

*)

(* Alternative Notations:

Notation out p := (output p).
Notation gate g p p' c := (gate _ _ _ g p (fun _ _ _ _ p' => c)).

Notation "p1 & p2 <<- p ; c" := (bind' p1 p2 p c) (at level 10, right associativity).
Notation "() <<-- p ; c" := (match elim_unit p with eq_refl => c end) (at level 10).
Notation "p' <-- 'gate g 'on' p ; C" := (gate' g p p' C) 
                                          (at level 10, right associativity).   
Notation "p <-- c1 ;; c2" := (comp' p c1 c2) (at level 10, right associativity).

Future work:
Notation gate' g p1 p2 c := (gate _ _ g p1 (fun _ _ _ z => match z (* w2? *) with
                                                        | p2 => c
                                                        end)).
*)

Definition id_circ {W} : Flat_Box W W.
  new_pat p W ∅ valid_empty.
(*  destruct (fresh_pat ∅ W valid_empty) as [Γ [_ p]]. *)
  box p (output p).
Defined.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Flat_Box W1 W2.
  new_pat p W1 ∅ valid_empty.
  new_pat p' W2 ∅ valid_empty.
  box p (
    p' ← gate g on p;
    output p'). 
Defined.

Definition new_discard : Flat_Box One One.
  new_pat p Bit ∅ valid_empty.
  box unit (
    p ← gate new0 on (); 
    unit ← gate discard on p;
    output () ).
Defined.

Definition init_discard : Flat_Box One One.
  new_pat q Qubit ∅ valid_empty.
  new_pat b Bit ∅ valid_empty.
  box () ( 
    q ← gate init0 on ();
    b ← gate meas on q;
    unit ← gate discard on b;
    output () ). 
Defined.

Definition hadamard_measure : Flat_Box Qubit Bit.
  new_pat q Qubit ∅ valid_empty.
  new_pat b Bit ∅ valid_empty.
  box q ( 
    q ← gate H on q;
    b ← gate meas on q;
    output b).
Defined.

(*
Definition lift_deutsch (U_f : Gate (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Box One Qubit.
  destruct (fresh_pat ∅ Qubit valid_empty) as [Γx [[Vx _] x]].
  destruct (fresh_pat Γx Qubit Vx) as [Γy [[Vy Dxy] y]].
  box (fun _ =>
    x     ← gate init0 on ();
    x     ← gate H on x;
    y     ← gate init1 on ();
    y     ← gate H on y;
    (x,y) ← gate U_f on (x,y);
    _     ← x;
    output y).
Defined.
*)

Definition deutsch (U_f : Gate (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Flat_Box One Qubit.
  new_pat x Qubit ∅ valid_empty.
  new_pat y Qubit Γ v.
  new_pat b Bit (Γ ⋓ Γ0) v2.
  box unit (
    x ← gate init0 on ();
    x ← gate H on x;
    y ← gate init1 on ();
    y ← gate H on y;
    (x,y) ← gate U_f on (x,y);
    b ← gate meas on x;
    () ← gate discard on b;
    output y).
Defined.

Definition init (b : bool) : Flat_Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.

Eval simpl in (init true).
Eval compute in (init true).

(*

Definition inSeq {W1 W2 W3} (c1 : Box W1 W2) (c2 : Box W2 W3) : Box W1 W3. 
  box (fun p1 => 
    letC p2 ← unbox c1 p1;
    unbox c2 p2).
Defined.

Definition inPar {W1 W2 W1' W2'} (c1 : Box W1 W1') (c2 : Box W2 W2') 
                                 : Box (W1⊗W2) (W1'⊗W2').
  box (fun p12 => 
    letC (p1,p2) ← output p12; 
    letC p1'     ← unbox c1 p1;
    letC p2'     ← unbox c2 p2; 
    output (p1',p2')).
Defined. 


(* Flip *)




(** Teleport **)

Definition bell00 : Box One (Qubit ⊗ Qubit).
  box (fun _ =>  
    letC a ← gate init0 ();
    letC b ← gate init0 ();
    letC a ← gate H a;
    gate CNOT (a,b)).
Defined.

Definition alice : Box (Qubit⊗Qubit) (Bit⊗Bit).
  box (fun qa => 
    letC (q,a) ← gate CNOT qa;
    letC q     ← gate H q;
    letC x     ← gate meas q;
    letC y     ← gate meas a;
    output (x,y)).
Defined.

Definition bob' : Box (Bit ⊗ (Bit ⊗ Qubit)) Qubit.
  box (fun xyb =>
    letC (x,yb)  ← output xyb;
    letC (y,b)   ← gate (bit_ctrl σx) yb;
    letC (x,b)   ← gate (bit_ctrl σx) (x,b);
    letC _       ← gate discard y;
    letC _       ← gate discard x;
    output b).
Defined.

(*
(* Explicit version for possible use in paper *)
Definition bob_ex : Box (Bit⊗Bit⊗Qubit) Qubit. 
refine(
  box (fun _ xyb =>
    let 'existT23 Γxy Γb xy b Mxyb := wproj xyb in
    let 'existT23 Γx Γy x y Mxy := wproj xy in
    HOASCircuits.gate _ _ _ (bit_ctrl σx) (y, b) 
     (fun _ _ _ _ yb =>
     let 'existT23 Γy' Γb' y' b' Myb := wproj yb in
      HOASCircuits.gate _ _ _ (bit_ctrl σz) (x, b') (* <? *)
       (fun _ _ _ _ xb =>
        HOASCircuits.gate _ _ _ discard y' 
         (fun _ _ _ _ z1 =>
          let 'existT23 Γx' Γb'' x' b'' Mxb := wproj xb in
          HOASCircuits.gate _ _ _ discard x'
           (fun _ _ _ _ z2 => HOASCircuits.output _ b'')))))); type_check. 
Defined.
*)

Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit.
(*  refine (box (fun _ xyb =>*)
  box (fun xyb => 
    letC ((x,y),b) ← output xyb ; 
(*    letC (x,y)  ← output xy ; *)
    letC (y,b)  ← gate (bit_ctrl σx) (y,b);
    letC (x,b)  ← gate (bit_ctrl σz) (x,b);
    letC _      ← gate discard y ;   
    letC _      ← gate discard x ;
    output b).
Defined.

Definition teleport' : Box Qubit Qubit.
  box (fun q =>
    letC (a,b) ← unbox bell00 () ;
    letC (x,y) ← unbox alice (q,a) ;
    unbox bob' (x,(y,b))).
Defined.

Definition teleport : Box Qubit Qubit.
  box (fun q =>
    letC (a,b) ← unbox bell00 () ;
    letC (x,y) ← unbox alice (q,a) ;
    unbox bob (x,y,b)).
Defined.

(* Right associative Tensor *)
Fixpoint Tensor (n : nat) (W : WType) := 
  match n with 
  | 0    => One
  | 1    => W
  | S n' => W ⊗ Tensor n' W
  end.

Infix "⨂" := Tensor (at level 30). 
(* Transparent Tensor. *)
Opaque Tensor.

Fixpoint inSeqMany {W} (n :nat) (c : Box W W) : Box W W := 
  match n with
  | 0 => id_circ
  | 1 => c
  | S n' => inSeq c (inSeqMany n' c)
  end.

(* Zero-indexed variant. I don't know why this is necessary *)
(* This will be fairly common *)
Fixpoint inParManyZ {W1 W2} (n : nat) (c : Box W1 W2) {struct n} : 
  Box (S n ⨂ W1) (S n ⨂ W2) :=
  match n with 
  | 0 => c
  | S n' => inPar c (inParManyZ n' c)
  end. 

Definition inParMany {W1 W2} (n : nat) (c : Box W1 W2) : Box (n ⨂ W1) (n ⨂ W2) := 
  match n with 
  | 0 => id_circ
  | S n' => inParManyZ n' c 
  end.


(** Quantum Fourier Transform **)

Parameter RGate : nat -> Unitary Qubit.

Fixpoint rotationsZ (m : nat) (n : nat) : Box (S (S n) ⨂ Qubit) (S (S n) ⨂ Qubit).
make_circ (
  match n as n0 return n = n0 -> Box (S (S n0) ⨂ Qubit) (S (S n0) ⨂ Qubit) with
  | 0    => fun _ => id_circ 
  | S n' => fun _ => box (fun _ w =>
      letC (c, qqs) ← output w;  
      letC (q, qs)  ← output qqs;  
      letC (c,qs)   ← unbox (rotationsZ m n') (c,qs) ;
      letC (c,q)    ← gate (ctrl (RGate (1 + m - n'))) (c,q);
      output (c,(q,qs)))
   end (eq_refl n)).
Defined.


Definition rotations (m : nat) (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => rotationsZ m n' 
  end.

Fixpoint qftZ (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit).
make_circ (
  match n as n0 return n = n0 -> Box (S n0 ⨂ Qubit) (S n0 ⨂ Qubit) with 
  | 0 => fun eq => box (fun _ p1 => gate H p1)
  | S n' => fun eq => box (fun _ qw =>
             letC (q,w) ← output qw; 
             letC w ← unbox (qftZ n') w; 
             unbox (rotationsZ (S n') n') (q,w))
  end (eq_refl n)).
Defined.

Definition qft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => qftZ n'
  end.



(** Invalid Circuits **)

Definition absurd_circ : Box Qubit (Bit ⊗ Qubit).
  box (fun w => 
    letC x  ← gate meas w ;
    letC w' ← gate H w ;
    output (x,w')).
Admitted.

Definition unused_qubit : Box Qubit One.
  box (fun w => 
   letC w ← gate H w ;
   output () ).
Admitted.

Definition clone : Box Qubit (Qubit ⊗ Qubit).
  box (fun w => output (w,w)).
Admitted.


(* Caught by Coq's typechecker
Definition split_qubit : Box Qubit (Qubit ⊗ Qubit).
  box (fun w => 
    ⟨w1,w2⟩  ← output w ;
    w2'      ← gate H w2 ; 
    output ⟨w1;w2'⟩). *)

*)

(* *)
