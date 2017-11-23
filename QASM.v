Require Import Reals.
Require Import String.

(* QASM.v - representation of QASM circuits *)

Definition id := string.

Inductive binop : Set :=
| plus | minus 
| times | div
| pow
.
    
Inductive unaryop : Set :=
| sin
| cos
| tan | e_to | ln | sqrt
| neg
.

Inductive exp : Set :=
| e_real (r:R)
| e_nat (n:nat)
| e_pi
| e_id (name:id)
| e_binop (e1:exp) (b:binop) (e2:exp)
| e_unop (u:unaryop) (e:exp)
.         

Inductive argument : Set :=
| a_id (n:id)
| a_idx (n:id) (i:nat)
.

Definition idlist := list id.
Definition anylist := list argument.
Definition explist := list exp.

Inductive uop : Set :=
| u_U (l:explist) (a:argument)
| u_CX (a1 a2:argument)
| u_app (i:id) (l:anylist)
| u_call (i:id) (es:explist) (l:anylist)
.

Inductive qop : Set :=
| q_uop (u:uop)
| q_meas (ain: argument) (aout: argument)
| q_reset (a:argument)
.          

Inductive gop : Set :=
| g_uop (u:uop)
| g_barrier (ids:idlist)
.

Definition goplist := list gop.  (* Nonempty? *)

Inductive decl : Set :=
| qreg (name:id) (size:nat)
| creg (name:id) (size:nat)
.

(*
gatedecl 
gate FOO ( ... ) <...> { ... } 
*)
Inductive statement : Set :=
| s_decl (d:decl)  
  (* TODO: what is the difference between args and names? are those the right terminology? *)
| s_gatedecl (name:id) (args:option idlist) (names:idlist) (body:goplist)
| s_opaque (name:id) (args:option idlist) (names:idlist)
| s_qop (q:qop)
| s_if (x:id) (n:nat) (q:qop)
| s_barrier (args:anylist)
| s_output (args:anylist)
.            

Definition program := list statement.

(** Convert from Minimal Circuits to QASM **)

(* [Min Circuit] to [QASM] translation procedure 
   1. Transform [Unitary] gates into a sequence of universal gates (ROT3 and CNOT).
      - See [min_circuit_translation_helper], [min_circuit_merge], 
            [unitary_gate_translation], [transpose_unitary_gate_circuit], 
            [append_gate_last], and [control_unitary_gate_circuit] functions.
   2. Translate the circuit into [QASM] program
      - See [trans], [trans'], [trans_exp], [pat_to_anylist], [meta_if], 
            [meta_if_true], and [meta_if_flase] functions.
*)

Require Import HOASCircuits.
Require Import HOASExamples.
Require Import FlatCircuits.
Require Import Contexts.
Require Import Arith.
Require Import Reals.
Require Import List.

Open Scope circ_scope.
Open Scope R_scope.
Import ListNotations.
Require Import Notations.

(* Universal gate representation for controlled universal gates

Universal gates - U(theta, phi, lambda) : rotation, cx : CNOT

// 1-parameter 0-pulse single qubit gate
gate u1(lambda) q { U(0,0,lambda) q; }
// controlled-U
gate cu3(theta,phi,lambda) c, t
{
  // implements controlled-U(theta,phi,lambda) with  target t and control c
  u1((lambda-phi)/2) t;
  cx c,t;
  u3(-theta/2,0,-(phi+lambda)/2) t;
  cx c,t;
  u3(theta/2,phi,0) t;
}

// 1-parameter 0-pulse single qubit gate
gate u1(lambda) q { U(0,0,lambda) q; }
// C3 gate: sqrt(S) phase gate
gate t a { u1(pi/4) a; }
// C3 gate: conjugate of sqrt(S)
gate tdg a { u1(-pi/4) a; }
// C3 gate: Toffoli
gate ccx a,b,c
{
  h c;
  cx b,c; tdg c;
  cx a,c; t c;
  cx b,c; tdg c;
  cx a,c; t b;
  t c; h c;
  cx a,b; t a; 
  tdg b;
  cx a,b;
}
*)
Fixpoint control_unitary_gate_circuit (cp : Pat) (C : Min_Circuit) : Min_Circuit :=
  match C with
  | min_gate g p C' =>
    match g with
    | (U u) =>
      match u with
      | ROT3 th ph la =>
        match cp with
        | c =>
          match p with
          | t =>
            min_gate (U (ROT3 0 0 ((la-ph)/2))) t
            (min_gate (U CNOT) (pair c t)
            (min_gate (U (ROT3 (-th/2) 0 (-(ph+la)/2))) t
            (min_gate (U CNOT) (pair c t)
            (min_gate (U (ROT3 (th/2) ph 0)) t
            (control_unitary_gate_circuit cp C')))))
          end
        end
      | CNOT => match p with
                | pair b c =>
                  match cp with
                  | a =>
                  min_gate (U (ROT3 (PI/2) 0 PI)) c
                  (min_gate (U CNOT) (pair b c) (min_gate (U (ROT3 0 0 (-PI/4))) c
                  (min_gate (U CNOT) (pair a c) (min_gate (U (ROT3 0 0 (PI/4))) c
                  (min_gate (U CNOT) (pair b c) (min_gate (U (ROT3 0 0 (-PI/4))) c
                  (min_gate (U CNOT) (pair a c) (min_gate (U (ROT3 0 0 (PI/4))) b
                  (min_gate (U (ROT3 0 0 (PI/4))) c (min_gate (U (ROT3 (PI/2) 0 PI)) c
                  (min_gate (U CNOT) (pair a b) (min_gate (U (ROT3 0 0 (PI/4))) a
                  (min_gate (U (ROT3 0 0 (-PI/4))) b
                  (min_gate (U CNOT) (pair a b)
                  (control_unitary_gate_circuit cp C')))))))))))))))
                  end
                | _ => (control_unitary_gate_circuit cp C')
                end
      | _ => (control_unitary_gate_circuit cp C')
      end
    | _ => (control_unitary_gate_circuit cp C')
    end
  | min_output p => min_output p
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (control_unitary_gate_circuit cp (f true))
                         | flase => (control_unitary_gate_circuit cp (f false))
                         end)
  end.

Fixpoint append_gate_last {W} (nu : Unitary W) (np : Pat) (c : Min_Circuit) : Min_Circuit :=
  match c with
  | min_output p => min_gate (U nu) np (min_output p)
  | min_gate g p c' => min_gate g p (append_gate_last nu np c')
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (append_gate_last nu np (f true))
                         | flase => (append_gate_last nu np (f false))
                         end)
  end.

Fixpoint transpose_unitary_gate_circuit (c : Min_Circuit) : Min_Circuit :=
  match c with
  | min_output p => min_output p
  | min_gate g p c' =>
    match g with
      | U u =>
        match u with
        | ROT3 th ph la =>
          append_gate_last (ROT3 (-th) (-ph) (-la)) p (transpose_unitary_gate_circuit c')
        | CNOT =>
          append_gate_last (CNOT) p (transpose_unitary_gate_circuit c')
        | _ => (transpose_unitary_gate_circuit c')
        end
      | _ => (transpose_unitary_gate_circuit c')
    end
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (transpose_unitary_gate_circuit (f true))
                         | false => (transpose_unitary_gate_circuit (f false))
                         end)
  end.

Fixpoint unitary_gate_translation {W} (u : Unitary W) (p po : Pat) : Min_Circuit :=
  match u with
    | H => min_gate (U (ROT3 (PI/2) 0 PI)) p (min_output po)
    | σx => min_gate (U (ROT3 PI 0 PI)) p (min_output po)
    | σy => min_gate (U (ROT3 PI (PI/2) (PI/2))) p (min_output po)
    | σz => min_gate (U (ROT3 0 0 PI)) p (min_output po)
    | CNOT => min_gate (U CNOT) p (min_output po)
    | ROT3 th ph la => min_gate (U (ROT3 th ph la)) p (min_output po)
    | ctrl u' =>
      match p with
      | pair p1 p2 =>
        control_unitary_gate_circuit p1 (unitary_gate_translation u' p2 po)
      | _ => unitary_gate_translation u' p po
      end
    | bit_ctrl u' => (* Todo : temporarily filled with [min_output po] *)
      (min_output po)
    | transpose u' => transpose_unitary_gate_circuit (unitary_gate_translation u' p po)
  end.

(* Merge c1 into c2 *)
Fixpoint min_circuit_merge (c1 c2 : Min_Circuit) : Min_Circuit :=
  match c1 with
  | min_output p => c2
  | min_gate g p c' => min_gate g p (min_circuit_merge c' c2)
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (min_circuit_merge (f true) c2)
                         | false => (min_circuit_merge (f false) c2)
                         end)
  end.

Fixpoint min_circuit_translation_helper (c : Min_Circuit) : Min_Circuit :=
  match c with
  | min_output p => min_output p
  | min_gate g p c' =>
    match g with
    | U u =>
      min_circuit_merge (unitary_gate_translation u p p) (min_circuit_translation_helper c')
    | _   => min_gate g p (min_circuit_translation_helper c')
    end
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (min_circuit_translation_helper (f true))
                         | false => (min_circuit_translation_helper (f false))
                         end)
  end.

(* Min Circuit Translation Helper Examples *)

Eval simpl in (match (hoas_to_min_box bell00 One) with
               | min_box W C => min_circuit_translation_helper C
               end).
Eval simpl in (match (hoas_to_min_box alice (Qubit ⊗ Qubit)) with
               | min_box W C => min_circuit_translation_helper C
               end).
Eval simpl in (match (hoas_to_min_box bob (Bit ⊗ Bit ⊗ Qubit)) with
               | min_box W C => min_circuit_translation_helper C
               end).
Eval simpl in (match (hoas_to_min_box teleport Qubit) with
               | min_box W C => min_circuit_translation_helper C
               end).


(* Translate [min circuit] to [QASM] *)

(** Naming functions for qreg, creg, and bits **)
Require Import Ascii.
(* Nat to string converter *)
Definition natToDigit (n : nat) : ascii :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.
Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match (n / 10)%nat with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.
Definition writeNat (n : nat) : string :=
  writeNatAux n n "".
(* naming function for qregs *)
Definition qname : nat -> id := fun x => String (ascii_of_nat 113) (writeNat x).
(* naming function for cregs *)
Definition cname : nat -> id := fun x => String (ascii_of_nat 99) (writeNat x).
(* name of the [creg array] used for branching *)
Definition bname : id := "bits"%string.

Fixpoint pow2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

(* meta_if : return [QASM] code equivalent to [if (bits[bn] == 1) then P1 else P2]  *)
Fixpoint meta_if_true (p1 : program) (bn : nat) : program :=
  match p1 with
  | [] => []
  | h :: p1' =>
    (match h with
     | s_if bname n q =>
       (s_if bname n q)
     | s_qop q =>
       (s_if bname 0 q)
     | _ => h
     end) :: (meta_if_true p1' bn)
  end.
Fixpoint meta_if_false (p2 : program) (bn : nat) : program :=
  match p2 with
  | [] => []
  | h :: p2' =>
    (match h with
     | s_if bname n q =>
       (s_if bname (n + (pow2 bn)) q)
     | s_qop q =>
       (s_if bname (pow2 bn) q)
     | _ => h
     end) :: (meta_if_false p2' bn)
  end.
Definition meta_if (p1 p2 : program) (bn : nat) : program :=
  (meta_if_true p1 bn) ++ (meta_if_false p2 bn).

(* trans c li n m : pair p d

   1. Description : A transition function from [min circuit] to [QASM] program.
   2. Input : 
     - c  : min circuit
     - li : context of min circuit (list of variable corresponding to its index)
     - n  : number of [qreg] or [creg] declared = argument for new variable name
            ([meas] gate operation creates [creg] variable of the same name with [qreg])
     - m  : size of [creg] array [bits] for branchgin
   3. Output :
     - p  : [QASM] program corresponding to c
     - d  : depth of branching (size of [creg] array [bits] used in p)

 *)
Fixpoint pat_to_anylist (li : list Var) (p : Pat) : anylist :=
  match p with
  | unit => []
  | qubit x => [a_id (qname (nth x li 0%nat))]
  | bit x => [a_id (cname (nth x li 0%nat))]
  | pair p1 p2 => (pat_to_anylist li p1) ++ (pat_to_anylist li p2)
  end.

(* trans_exp : translate real numbers to [exp] *)
Definition trans_exp (r : R) : exp := (* Todo : temporarily filled with [e_pi] *)
  e_pi.

Fixpoint trans' (c : Min_Circuit) (li : list Var) (n m : nat) :=
  match c with
  | min_output p    => ([s_output (pat_to_anylist li p)], 0%nat)
  | min_gate g p c' =>
    match g with
    | U u     =>
      let (p', d') := (trans' c' li n m) in
      (((match u with
         | CNOT =>
           (match p with
            | pair (qubit x1) (qubit x2) =>
              let qx1 := (nth x1 li 0%nat) in
              let qx2 := (nth x2 li 0%nat) in
              let a1 := (a_id (qname qx1)) in
              let a2 := (a_id (qname qx2)) in
              [s_qop (q_uop (u_CX a1 a2))]
            | _ => []
            end) 
         | ROT3 th ph la =>
           (match p with
            | qubit x =>
              let qx := (nth x li 0%nat) in
              let a := (a_id (qname qx)) in
              [s_qop (q_uop (u_U [(trans_exp th); (trans_exp ph); (trans_exp la)] a))]
            | _ => []
            end)
         | _ => []
         end) ++ p'), d')
    | init0   =>
      let (p', d') := (trans' c' (li ++ [n]) (S n) m) in
      (([s_decl (qreg (qname n) 1)] ++ p'), d')
    | init1   =>
      let (p', d') := (trans' c' (li ++ [n]) (S n) m) in
      (([s_decl (qreg (qname n) 1);
           s_qop (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname n))))] ++ p'), d')
    | new0    =>
      let (p', d') := (trans' c' (li ++ [n]) (S n) m) in
      (([s_decl (creg (cname n) 1)] ++ p'), d')
    | new1    =>
      let (p', d') := (trans' c' (li ++ [S n]) (S (S n)) m) in
      (([s_decl (creg (cname (S n)) 1); s_decl (qreg (qname n) 1);
           s_qop (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname n))));
           s_qop (q_meas (a_id (qname n)) (a_id (cname (S n))))]
          ++ p'), d')
    | meas    =>
      let (p', d') := (trans' c' li n m) in
      ((match p with
        | qubit x =>
          let a := (nth x li 0%nat) in
          ([s_decl (creg (cname a) 1);
              s_qop (q_meas (a_id (qname a)) (a_id (cname a)))]
             ++ p')
        | _ => []
        end), d')
    | discard =>
      match p with
      | bit x =>
        let li' := List.remove Nat.eq_dec x li in
        (trans' c' li' n m)
      | _ => ([], 0%nat)
      end
    end
  | min_lift p f =>
    match p with
    | bit x => ([(* Todo *)], 0%nat)
    | qubit x =>
      let li' := List.remove Nat.eq_dec x li in
      let (p1, d1) := (trans' (f true) li' n m) in
      let (p2, d2) := (trans' (f false) li' n m) in
      let bn := (Nat.max d1 d2) in
      let a := (nth x li 0%nat) in
      (([s_decl (creg (cname a) 1);
           s_qop (q_meas (a_id (qname a)) (a_id (cname a)))]
          ++ (meta_if p1 p2 bn)), (S bn))
    | _ => ([], 0%nat)
    end
  end.
Fixpoint trans (c : Min_Circuit) (w : WType) : program :=
  let (p, n) := fresh_pat w 0 in
  let li := pat_to_list p in
  let (qasm, d) := (trans' c li n 0%nat) in
  (match d with
   | 0 => qasm
   | S _ =>
     [s_decl (creg bname d)] ++ qasm
   end).

(* Min Circuit Translation Examples *)
Eval simpl in trans (match (hoas_to_min_box bell00 One) with
                     | min_box W C => min_circuit_translation_helper C
                     end) One.
Eval simpl in trans (match (hoas_to_min_box alice (Qubit ⊗ Qubit)) with
                     | min_box W C => min_circuit_translation_helper C
                     end) (Qubit ⊗ Qubit).
Eval simpl in trans (match (hoas_to_min_box bob (Bit ⊗ Bit ⊗ Qubit)) with
                     | min_box W C => min_circuit_translation_helper C
                     end) (Bit ⊗ Bit ⊗ Qubit).
Eval simpl in trans (match (hoas_to_min_box teleport Qubit) with
                     | min_box W C => min_circuit_translation_helper C
                     end) Qubit.

Close Scope circ_scope.
