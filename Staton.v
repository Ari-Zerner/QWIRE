Require Import String.
Require Import Quantum.
Require Import Coq.Classes.SetoidClass.

Definition var := string.

Definition context := list var.

Definition gate n := Square (2 ^ n).

Hint Unfold gate.

Inductive term :=
| continue (name: string) (ctx: context)
| new (a: var) (t: term)
| measure (a: var) (t u: term)
| apply_gate {n} (g: gate n) (a_params b_params: context) (t: term).

Definition WF_Context := @NoDup var.

Hint Unfold WF_Context.

Lemma WF_Context_nil: WF_Context [].
Proof. apply NoDup_nil. Qed.

Lemma WF_Context_singleton: forall a, WF_Context [a].
Proof.
  intros. apply NoDup_cons. auto. apply NoDup_nil.
Qed.

Definition CEquiv (c1 c2: context) :=
  forall a, In a c1 <-> In a c2.

Hint Unfold CEquiv.

Instance CEquiv_refl: Reflexive CEquiv.
Proof.
  unfold Reflexive, CEquiv. intros. reflexivity.
Qed.

Instance CEquiv_sym: Symmetric CEquiv.
Proof.
  unfold Symmetric, CEquiv. intros. rewrite (H a). reflexivity.
Qed.

Instance CEquiv_trans: Transitive CEquiv.
Proof.
  unfold Transitive, CEquiv. intros. rewrite (H a). rewrite (H0 a). reflexivity.
Qed.

Instance CEquiv_equiv: Equivalence CEquiv := {}.

Instance context_setoid: Setoid context := {}.

Inductive WF_Term: context -> term -> Prop :=
| wf_continue (name: string) (c1 c2: context):
    WF_Context c1 ->
    WF_Context c2 ->
    CEquiv c1 c2 ->
    WF_Term c1 (continue name c2)
| wf_new (c: context) (a: var) (t: term):
    WF_Context (a :: c) ->
    WF_Term (a :: c) t ->
    WF_Term c (new a t)
| wf_measure (c: context) (a: var) (t u: term):
    WF_Context (a :: c) ->
    WF_Term c t ->
    WF_Term c u ->
    WF_Term (a :: c) (measure a t u)
| wf_apply_gate {n} (g: gate n) (c a_params b_params: context) (t: term):
    @WF_Unitary (2^n) g ->
    WF_Context (b_params ++ c) ->
    WF_Context (a_params ++ c) ->
    length b_params = n ->
    length a_params = n ->
    WF_Term (b_params ++ c) t ->
    WF_Term (a_params ++ c) (apply_gate g a_params b_params t).

(* shorthands for continuations *)
Definition apply_X := @apply_gate 1 σx.
Definition apply_Y := @apply_gate 1 σy.
Definition apply_Z := @apply_gate 1 σz.
Definition apply_swap := @apply_gate 2 swap.
Definition apply_I (a: context) := @apply_gate (length a) (I (length a)) a.
Definition apply_Had := @apply_gate 1 hadamard.
Definition apply_cnot := @apply_gate 2 cnot.
Definition new0 (a: var) (x: term) := new a (apply_X [a] [a] x).
Definition rename_vars (a b: context) (x: term) := apply_I a b x.

(* I couldn't find this in the library, so I defined it here.
   If I end up needing a lot of lemmas about it, I'll look more thoroughly. *)
Definition Block_Diag {n} (M N: gate n) (D: gate (S n)) := forall x y,
    D x y = M x y \/ (2^n <= x /\ 2^n <= y)%nat.

Definition block_diag {n} (M N: gate n): gate (S n) :=
  fun x y => if (2^n <=? x) && (2^n <=? y) then N (x - 2^n)%nat (y - 2^n)%nat else M x y.

Lemma block_diag_Block_Diag: forall n M N, @Block_Diag n M N (block_diag M N).
Proof.
  unfold Block_Diag. intros.
  destruct (2^n <=? x) eqn:Ex, (2^n <=? y) eqn:Ey;
    unfold block_diag; rewrite Ex; rewrite Ey; simpl.
  - right. split; apply leb_complete; assumption.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
Qed.

Fixpoint discard (a: context) (t: term) :=
  match a with
  | [] => t
  | a' :: b => measure a' (discard b t) (discard b t)
  end.

Inductive QEquiv: term -> term -> Prop :=
| qequiv_refl (x: term):
    QEquiv x x
| qequiv_sym (x y: term):
    QEquiv x y ->
    QEquiv y x
| qequiv_trans (x y z: term):
    QEquiv x y ->
    QEquiv y z ->
    QEquiv x z
| qequiv_cong_new (a: var) (x x': term):
    QEquiv x x' ->
    QEquiv (new a x) (new a x')
| qequiv_cong_measure (a: var) (x x' y' y: term):
    QEquiv x x' ->
    QEquiv y y' ->
    QEquiv (measure a x y) (measure a x' y')
| qequiv_cong_apply_gate {n} (U: gate n) (a b: context) (x x': term):
    QEquiv x x' ->
    QEquiv (apply_gate U a b x) (apply_gate U a b x')
| axiom_a (a: var) (x y: term):
    QEquiv (apply_X [a] [a] (measure a x y))
           (measure a y x)
| axiom_b {n} (a: var) (U V: gate n) (D: gate (S n)) (b: context) (x y: term):
    Block_Diag U V D ->
    QEquiv (measure a (apply_gate U b b x) (apply_gate V b b y))
           (apply_gate D (a :: b) (a :: b) (measure a x y))
| axiom_c {n} (U: gate n) (a: context) (x: term):
    QEquiv (apply_gate U a a (discard a x))
           (discard a x)
| axiom_d (a: var) (x y: term):
    QEquiv (new a (measure a x y))
           x
| axiom_e {n} (a: var) (U V: gate n) (D: gate (S n)) (b: context) (x: term):
    Block_Diag U V D ->
    QEquiv (new a (apply_gate D (a :: b) (a :: b) x))
           (apply_gate U b b (new a x))
| axiom_f (a b: var) (x: var -> var -> term):
    QEquiv (apply_swap [a; b] [a; b] (x a b))
           (x b a)
| axiom_g (a: context) (x: term):
    QEquiv (apply_I a a x)
           x
| axiom_h {n} (U V: gate n) (a: context) (x: term):
    QEquiv (apply_gate (@Mmult (2^n) (2^n) (2^n) U V) a a x)
           (apply_gate U a a (apply_gate V a a x))
| axiom_i {m n} (U: gate m) (V: gate n) (a: context) (b: context) (x: term):
    QEquiv (@apply_gate (m+n) (@kron (2^m) (2^m) (2^n) (2^n) U V) (a ++ b) (a ++ b) x)
           (apply_gate U a a (apply_gate V b b x))
| axiom_j (a b: var) (x y u v: term):
    QEquiv (measure a (measure b u v) (measure b x y))
           (measure b (measure a u x) (measure a v y))
| axiom_k (a b: var) (x: term):
    QEquiv (new a (new b x))
           (new b (new a x))
| axiom_l (a b: var) (x y: term):
    QEquiv (new a (measure b x y))
           (measure b (new a x) (new a y)).

Instance QEquiv_refl: Reflexive QEquiv := qequiv_refl.

Instance QEquiv_sym: Symmetric QEquiv := qequiv_sym.

Instance QEquiv_trans: Transitive QEquiv := qequiv_trans.

Instance QEquiv_equiv: Equivalence QEquiv := {}.

Instance term_setoid: Setoid term := {}.

(* Example derivations. *)

(* Rotation about Z doesn't affect standard basis measurement. *)

Definition example_1 theta a x y :=
    @apply_gate 1 (phase_shift theta) [a] [a]
               (measure a (continue x []) (continue y [])).

Example WF_example_1: forall theta a x y,
    WF_Term [a] (example_1 theta a x y).
Proof.
  unfold example_1. intros.
  apply wf_apply_gate with (a_params := [a]).
  apply phase_unitary.
  apply WF_Context_singleton.
  apply WF_Context_singleton.
  reflexivity.
  reflexivity.
  apply wf_measure.
  apply WF_Context_singleton.
  apply wf_continue.
  apply WF_Context_nil.
  apply WF_Context_nil.
  apply CEquiv_refl.
  apply wf_continue.
  apply WF_Context_nil.
  apply WF_Context_nil.
  apply CEquiv_refl.
Qed.

Example deriv_example_1: forall theta a x y,
    QEquiv (example_1 theta a x y)
           (measure a (continue x []) (continue y [])).
Proof.
  unfold example_1. intros.
  remember (fun x y => if (x =? 0) && (y =? 0) then Cexp theta else C0) as M.
  assert (@Block_Diag 0 (I 1) M (phase_shift theta)).
  - unfold Block_Diag. intros. destruct x0 eqn:Ex, y0 eqn:Ey; try (left; reflexivity).
    + left. unfold phase_shift, I. simpl. destruct n; reflexivity.
    + right. split; simpl; omega.
  - apply qequiv_trans with (y := measure a (@apply_gate 0 (I 1) [] [] (continue x []))
                                            (@apply_gate 0 M     [] [] (continue y []))).
    apply qequiv_sym.
    eapply axiom_b.
    assumption.
    eapply qequiv_cong_measure.
    replace (continue x []) with (discard [] (continue x [])).
    eapply axiom_c.
    reflexivity.
    replace (continue y []) with (discard [] (continue y [])).
    eapply axiom_c.
    reflexivity.
Qed.

Definition example_2 a b x :=
  new0 a (apply_Had [a] [a] (measure a (continue x [b]) (apply_Z [b] [b] (continue x [b])))).

Example WF_example_2: forall a b x,
    a <> b ->
    WF_Term [b] (example_2 a b x).
Proof.
  unfold example_2. intros. unfold new0, apply_Had, apply_X, apply_Z.
  assert (WFC: WF_Context [a; b]).
  unfold WF_Context.
  apply NoDup_cons.
  apply not_in_cons. split; auto.
  apply WF_Context_singleton.
  eapply wf_new. apply WFC.
  eapply wf_apply_gate with (a_params := [a]).
  apply σx_unitary.
  apply WFC. apply WFC. reflexivity. reflexivity.
  eapply wf_apply_gate. apply H_unitary.
  apply WFC. apply WFC. reflexivity. reflexivity.
  eapply wf_measure.
  apply WFC.
  apply wf_continue.
  apply WF_Context_singleton.
  apply WF_Context_singleton.
  reflexivity.
  eapply wf_apply_gate with (a_params := [b]).
  apply σz_unitary.
  apply WF_Context_singleton.
  apply WF_Context_singleton.
  reflexivity. reflexivity.
  apply wf_continue.
  apply WF_Context_singleton.
  apply WF_Context_singleton.
  reflexivity.
Qed.

Example deriv_example_2: forall a b x,
    QEquiv (example_2 a b x)
           (measure b (new0 a (continue x [a])) (new a (continue x [a]))).
Proof.
  (* Future work: This may need infrastructure for alpha-conversion,
     although axiom F might suffice here. *)
Admitted.

