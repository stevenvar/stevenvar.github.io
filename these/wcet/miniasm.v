Require Import String.

Notation "'let' 'val' x ':=' t 'in' u" :=
  (match t with
   | Some x => u
   | None => None
   end)
    (at level 200, x ident, t at level 100, u at level 200, only parsing).

Notation "'let' 'val' ( x , y ) ':=' t 'in' u" :=
  (match t with
   | Some (x, y) => u
   | None => None
   end)
    (at level 200, x ident, t at level 100, u at level 200, only parsing).

Notation "'let' 'val' ( x , y , z ) ':=' t 'in' u" :=
  (match t with
   | Some (x, y, z) => u
   | None => None
   end)
    (at level 200, x ident, t at level 100, u at level 200, only parsing).

Notation "'ret' e" := (Some e) (at level 200, only parsing).
Notation "'exit'" := None (at level 200, only parsing).

Notation "e '==?' v" := (e = Some v) (at level 70, only parsing).

Definition var := string.

(** * The idealized language **)

(** The mini-language instructions :  **)

Inductive instr :=
| Init : var -> nat -> instr (* x = 3 *)
| Assign : var -> var -> instr (* x = y *)
| Addv : var -> var -> instr (* x += y *)
| Subv : var -> var -> instr (* x -= y *)
| Branch : nat -> instr (* branch 42 *)
| Branchif : var -> nat -> instr (* branch x 42 *)
| Return : instr.

Open Scope list_scope.
Require Import List.


(** Some useful functions : **)

Definition eq_var x y := if string_dec x y then true else false.

Require Import Arith.
Definition eq_nat x y := x =? y.

Fixpoint assoc_opt {A} {B} (f: A -> A -> bool) (x:A) (l:list (A * B)) : option B :=
  match l with
   | (y,k)::l => if f x y then Some k else assoc_opt f x l
   | nil => None
  end.

Notation assoc_var := (assoc_opt eq_var).
Notation assoc_instr := (assoc_opt eq_nat).
Notation program := (list (nat * instr)).

Fixpoint assign {A} {B} (f: A -> A -> bool) (x:A) (v:B) (l:list (A * B)) : list (A * B) :=
  match l with
  | nil => (x,v)::l
  | (y,k)::l => if f x y then (y,v)::l else (y,k)::assign f x v l
  end.

Notation assign_var := (assign eq_var).

Definition lifted_plus v w :=
  let val n := v in
  let val m := w in
  ret n + m.

Definition lifted_minus v w :=
  let val n := v in
  let val m := w in
  ret n - m.

Local Open Scope string_scope.


(** A state is a program * a code pointer * a memory  **)

Definition state : Type := list (nat * instr) * nat * list (var * option nat).

(** The step function of the mini-language : **)

Fixpoint step_opt (st : state): option state :=
  match st with
  | (p, pc, m) =>
    match assoc_instr pc p with
    | Some i =>
      match i with
      | Init x n =>
        ret (p, pc + 1, assign_var x (Some n) m)
      | Assign x y =>
        let val w := assoc_var y m in
        ret (p, pc + 1, assign_var x w m)
      | Addv x y =>
        let val v := assoc_var x m in
        let val w := assoc_var y m in
        let k := lifted_plus v w in
        ret (p, pc + 1, assign_var x k m)
      | Subv x y =>
        let val v := assoc_var x m in
        let val w := assoc_var y m in
        let k := lifted_minus v w in
        ret (p, pc + 1, assign_var x k m)
      | Branch n => ret (p, n, m)
      | Branchif x n =>
        let val v := assoc_var x m in
        match v with
        | Some a => if eq_nat a 0 then ret (p, pc + 1, m) else ret (p, n, m)
        | None => exit
        end
      | Return => exit
      end
    | None => exit
    end
  end.

(** The deterministic small-step semantics of the mini-lang : **)


Inductive det_sem : state -> state -> Prop :=
| Step_1 : forall p pc m x n,
    assoc_instr pc p ==? (Init x n) ->
    det_sem (p, pc, m) (p, pc + 1, assign eq_var x (Some n) m)
| Step_2 : forall p pc m x y w,
    assoc_instr pc p ==? (Assign x y) ->
    assoc_var y m ==? w ->
    det_sem (p, pc, m) (p, pc + 1, assign eq_var x w m)
| Step_3 : forall p pc m x y v w,
    assoc_instr pc p ==? (Addv x y) ->
    assoc_var x m ==? v ->
    assoc_var y m ==? w ->
    det_sem (p, pc, m) (p, pc + 1, assign eq_var x (lifted_plus v w) m)
| Step_4 : forall p pc m x y v w,
    assoc_instr pc p ==? (Subv x y) ->
    assoc_var x m ==? v ->
    assoc_var y m ==? w ->
    det_sem (p, pc, m) (p, pc + 1, assign eq_var x (lifted_minus v w) m)
| Step_5 : forall p pc m n,
    assoc_instr pc p ==? (Branch n) ->
    det_sem (p, pc, m) (p, n, m)
| Step_6 : forall p pc m x n,
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? (Some 0) ->
    det_sem (p, pc, m) (p, pc + 1, m)
| Step_7 : forall p pc m x n k,
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? (Some (S k)) ->
    det_sem (p, pc, m) (p, n, m)
.

(** Proof that the function and the inductive relation are the same :  **)


Lemma step_opt_det_sem : forall s s' , step_opt s = Some s' <-> det_sem s s'.
Proof.
  intros.
  - split.
    intros.
    destruct s as ((p,pc),m).
    unfold step_opt in H.
    destruct (assoc_instr pc p) eqn:Ha.
    destruct i eqn:Hi.
    + inversion H.
      subst.
      clear H.
      econstructor.
      auto.
    + destruct (assoc_var v0 m) eqn : Hv.
      inversion H.
      subst.
      clear H.
      econstructor.
      eauto.
      auto.
      inversion H.
    + destruct (assoc_var v m) eqn : Hv.
      destruct (assoc_var v0 m) eqn : Hv0.
      inversion H.
      subst.
      clear H.
      eapply Step_3.
      eauto.
      auto.
      auto.
      inversion H.
      inversion H.
    + destruct (assoc_var v m) eqn : Hv.
      destruct (assoc_var v0 m) eqn : Hv0.
      inversion H.
      subst.
      clear H.
      eapply Step_4.
      eauto.
      auto.
      auto.
      inversion H.
      inversion H.
    + inversion H.
      subst.
      clear H.
      econstructor.
      auto.
    + destruct (assoc_var v m) eqn : Hv.
      destruct o eqn: Ho.
      destruct (eq_nat n0 0) eqn : Hn.
      inversion H.
      subst.
      clear H.
      eapply Step_6.
      eauto.
      unfold eq_nat in Hn.
      apply beq_nat_true in Hn.
      subst.
      auto.
      subst.
      inversion H.
      subst.
      clear H.
      apply beq_nat_false in Hn.
      destruct n0.
      contradiction.
      eapply Step_7 with (k:=n0).
      eauto.
      eauto.
      inversion H.
      inversion H.
    + inversion H.
    + inversion H.
    + intros.
      induction H.
      -- simpl.
         rewrite H. auto.
      -- simpl. rewrite H. rewrite H0. auto.
      -- simpl. rewrite H. rewrite H0. rewrite H1. auto.
      -- simpl. rewrite H. rewrite H0. rewrite H1. auto.
      -- simpl. rewrite H. auto.
      -- simpl. rewrite H. rewrite H0. simpl. auto.
      -- simpl. rewrite H. rewrite H0. simpl. auto.
Qed.

(** * Non-deterministic semantics and erasures **)

(** Some variables values might not be known at compile time : we introduce a
  non-deterministic semantics for dealing with this **)

Inductive nondet_sem: state -> state -> Prop :=
| ND_Step_1 : forall p pc m x n,
    assoc_instr pc p ==? (Init x n) ->
    nondet_sem (p, pc, m) (p, pc + 1, assign eq_var x (Some n) m)
| ND_Step_2 : forall p pc m x y w,
    assoc_instr pc p ==? (Assign x y) ->
    assoc_var y m ==? w ->
    nondet_sem (p, pc, m) (p, pc + 1, assign eq_var x w m)
| ND_Step_3 : forall p pc m x y v w,
    assoc_instr pc p ==? (Addv x y) ->
    assoc_var x m ==? v ->
    assoc_var y m ==? w ->
    nondet_sem (p, pc, m) (p, pc + 1, assign eq_var x (lifted_plus v w) m)
| ND_Step_4 : forall p pc m x y v w,
    assoc_instr pc p ==? (Subv x y) ->
    assoc_var x m ==? v ->
    assoc_var y m ==? w ->
    nondet_sem (p, pc, m) (p, pc + 1, assign eq_var x (lifted_minus v w) m)
| ND_Step_5 : forall p pc m n,
    assoc_instr pc p ==? (Branch n) ->
    nondet_sem (p, pc, m) (p, n, m)
| ND_Step_6 : forall p pc m x n,
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? (Some 0) ->
    nondet_sem (p, pc, m) (p, pc + 1, m)
| ND_Step_7 : forall p pc m x n k,
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? (Some (S k)) ->
    nondet_sem (p, pc, m) (p, n, m)
| ND_Step_8 : forall p pc m x n, (* non-deterministic rules *)
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? None ->
    nondet_sem (p, pc, m) (p, pc + 1, m)
| ND_Step_9 : forall p pc m x n,
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? None ->
    nondet_sem (p, pc, m) (p, n, m)
.





  (** An erased memory is a memory with less known variables (unknown variable = None value)  : **)

Inductive erased : list (var * option nat) -> list (var * option nat) -> Prop :=
| Erased_1: forall x v tl1 tl2,
    erased tl1 tl2 ->
    erased ((x, v) :: tl1) ((x, v) :: tl2)
| Erased_2: forall x a tl1 tl2,
    erased tl1 tl2 ->
    erased ((x, Some a) :: tl1) ((x, None) :: tl2)
| Erased_3: erased nil nil
.


(** An erased state contains an erased memory **)

Inductive state_erased: state -> state -> Prop :=
| State_Erased : forall p pc m1 m2,
    erased m1 m2 ->
    state_erased (p, pc, m1) (p, pc, m2).



(** A (deterministic) run follows the deterministic semantics upto a return instruction **)

Inductive run: state -> (list state) -> Prop :=
| Run_1 :  forall p pc m, (* final state *)
    assoc_instr pc p ==? Return ->
    run (p, pc, m) ((p, pc, m)::nil)
| Run_2 : forall st st' r,
    step_opt st ==? st' ->
    run st' r ->
    run st (st::r)
.


Lemma run_init : forall s s' T , run s (s'::T) -> s = s'.
Proof.
  intros.
  inversion H.
  - auto.
  - auto.
Qed.


(** Every transition in the deterministic semantics exists in the non-deterministic semantics **)
Lemma embedding : forall s s' , (det_sem s s') -> (nondet_sem s s').
      Proof.
  intros.
  induction H.
  - econstructor.
    auto.
  - econstructor.
    eauto.
    auto.
  - eapply ND_Step_3.
    eauto. auto. auto.
  - eapply ND_Step_4.
    eauto. auto. auto.
  - econstructor. auto.
  - eapply ND_Step_6.
    eauto. auto.
  - eapply ND_Step_7.
    eauto. eauto.
Qed.



(** We use a cost function to compute the cost of a run **)

(** First a function giving each instruction a cost **)
Parameter instr_cost : instr -> nat.

(** The function that computes the cost associated with a state **)

Definition step_cost {A} (st: (program * nat * A)) :=
  match st with
  | (p, pc, m) =>
    match assoc_instr pc p with
    | None => None
    | Some i => Some (instr_cost i)
    end
  end.

(** The cost of a run **)

Fixpoint cost {A} (r: list (program * nat * A)) :=
  match r with
  | nil => 0
  | (st :: t) =>
    match step_cost st with
    | Some k => k + cost t
    | None => 0 (* Return or error *)
    end
  end.



(** An erased trace is a run with all its states (more or less) erased **)

Inductive erased_trace: list state -> list state -> Prop :=
| Erased_Trace_1 :
    erased_trace nil nil
| Erased_Trace_2 : forall st1 st1' T1 T1',
    state_erased st1 st1' ->
    erased_trace T1 T1' ->
    erased_trace (st1::T1) (st1'::T1').

(** * Costs **)


(** The cost of a step is the same even with an erased memory **)

Lemma step_cost_erased_is_equal : forall s s' , state_erased s s' -> step_cost (s) = step_cost(s').
Proof.
  intros.
  inversion H.
  subst.
  simpl.
  auto.
Qed.


(** The cost of an erased trace is the same as the initial trace **)

Lemma trace_cost_erased_is_equal : forall T T', erased_trace T T' -> cost(T) = cost(T').
Proof.
  intros.
  induction H.
  - simpl. auto.
  - simpl.
    rewrite IHerased_trace.
    apply step_cost_erased_is_equal in H.
    rewrite H.
    auto.
Qed.

(** max run cost computes the most expensive cost of an (erased) program : if there is ambiguity as to
  which branch to take, the max run takes the branch with the greater cost **)

Inductive max_run_cost : state -> nat -> Prop :=
| Max_Run_Cost_1 : forall p pc m, (* final state *)
    assoc_instr pc p ==? Return ->
    max_run_cost (p, pc, m) (instr_cost Return)
| Max_Run_Cost_2 : forall st st' c k,
    step_opt st ==? st' ->
    step_cost st ==? c ->
    max_run_cost st' k ->
    max_run_cost st (c + k)
| Max_Run_Cost_3 : forall p pc m x n c k k', (* non-deterministic rules *)
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? None ->
    step_cost (p, pc, m) ==? c ->
    max_run_cost (p, pc + 1, m) k ->
    max_run_cost (p, n, m) k' ->
    k > k' ->
    max_run_cost (p, pc, m) (c + k)
| Max_Run_Cost_4 : forall p pc m x n c k k', (* non-deterministic rules *)
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? None ->
    step_cost (p, pc, m) ==? c ->
    max_run_cost (p, pc + 1, m) k ->
    max_run_cost (p, n, m) k' ->
    k <= k' ->
    max_run_cost (p, pc, m) (c + k').

(** Another definition of max run cost **)
Inductive max_run_cost2 : state -> nat -> Prop :=
| Max_Run_Cost2_1 : forall p pc m, (* final state *)
    assoc_instr pc p ==? Return ->
    max_run_cost2 (p, pc, m) (instr_cost Return)
| Max_Run_Cost2_2 : forall st st' c k,
    step_opt st ==? st' ->
    step_cost st ==? c ->
    max_run_cost2 st' k ->
    max_run_cost2 st (c + k)
| Max_Run_Cost2_3 : forall p pc m x n c k k', (* non-deterministic rules *)
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? None ->
    step_cost (p, pc, m) ==? c ->
    max_run_cost2 (p, pc + 1, m) k ->
    max_run_cost2 (p, n, m) k' ->
    max_run_cost2 (p, pc, m) (c + max k k').

Require Import Omega.


Lemma max_is_max : forall k k' , k > k' -> max k k' = k.
Proof.
  intros k.
  induction k.
  - intros. inversion H.
  - intros. simpl.
    destruct k'.
    + auto.
    + rewrite IHk.
      auto.
      omega.
Qed.

Lemma max_is_max2 : forall k k', k <= k' -> max k k' = k'.
Proof.
  intros k k'.
  generalize dependent k.
  induction k'.
  - intros. inversion H. simpl. auto.
  - intros. destruct k.
    + simpl. auto.
    + simpl.
      rewrite IHk'.
      auto.
      omega.
Qed.

Lemma max_run_max1 : forall s k k' ,  max_run_cost s k -> k > k' -> max_run_cost s (Init.Nat.max k k') .
Proof.
  intros.
  apply max_is_max in H0.
  rewrite H0.
  auto.
Qed.

Lemma max_run_max2 : forall s k k' ,  max_run_cost s (k') -> k <= k' -> max_run_cost s (Init.Nat.max k k') .
Proof.
  intros.
  apply max_is_max2 in H0.
  rewrite H0.
  auto.
Qed.


(** The two definitions of max run cost are equivalent **)
Lemma max_run_cost_equiv_max_run_cost2 : forall s k , max_run_cost s k <-> max_run_cost2 s k.
Proof.
  intros.
  split.
  - intros.
    + induction H.
      -- econstructor.
         auto.
      -- econstructor. eauto.
         eauto.
         eauto.
      -- apply max_is_max in H4.
         rewrite <- H4.
         eapply Max_Run_Cost2_3.
         eauto.
         auto.
         auto.
         auto.
         auto.
      -- apply max_is_max2 in H4.
         rewrite <- H4.
         eapply Max_Run_Cost2_3.
         eauto.
         auto.
         auto.
         auto.
         auto.
  - intros.
    induction H.
    + econstructor. auto.
    + econstructor. eauto.
      auto.
      auto.
    + case_eq (leb k k').
      -- intros.
         rewrite Nat.leb_le in H4.
         apply max_is_max2 in H4.
         eapply Max_Run_Cost_4.
         eauto.
         auto.
         auto.
         eauto.
         rewrite H4.
         eauto.
         Search (_ <= max _ _).
         apply Nat.le_max_l.
      -- intros.
         Search ( ( _ <=? _ ) ).
         apply leb_complete_conv in H4.
         assert (k> k').
         auto.
         apply max_is_max in H4.
         rewrite H4.
         eapply Max_Run_Cost_3.
         eauto.
         auto.
         auto.
         auto.
         eauto.
         auto.
Qed.

(** The cost of a step is unique : there is no other identical step with a different cost  **)
Lemma step_cost_is_unique : forall (s:state) k k' , step_cost s = Some k -> step_cost s = Some k' -> k = k'.
Proof.
  intros.
  destruct s as ((p,pc),m).
  simpl in H.
  simpl in H0.
  destruct k.
  - destruct k'.
    + auto.
    + destruct assoc_instr.
      rewrite H in H0. discriminate.
      inversion H.
  - destruct k'.
    + destruct assoc_instr.
      rewrite H in H0. discriminate.
      inversion H.
    + destruct assoc_instr.
      rewrite H in H0.
      inversion H0.
      subst.
      auto.
      inversion H.
Qed.



(** The maximum cost is unique : there are no two identical computation of max_run_cost that give different results **)
Lemma max_run_cost_is_unique : forall s k , max_run_cost s k -> forall k' , max_run_cost s k' -> k = k'.
Proof.
  intros s k H.
  induction H.
  - intros. inversion H0.
    + subst. auto.
    + inversion H1. rewrite H in H7. discriminate.
    + subst. rewrite H in H4. discriminate.
    + subst. rewrite H in H4. discriminate.
  - intros. inversion H2.
    + subst.  inversion H.
      rewrite H3 in H5. discriminate.
    + subst.
      assert (c = c0).
      eapply step_cost_is_unique.
      eauto. eauto.
      subst.
      assert (k = k0).
      apply IHmax_run_cost.
      rewrite H in H3.
      inversion H3.
      subst.
      auto.
      subst.
      auto.
    + subst.
      inversion H.
      rewrite H3 in H10.
      rewrite H4 in H10.
      discriminate.
    + subst.
      inversion H.
      rewrite H3 in H10.
      rewrite H4 in H10.
      discriminate.
  - intros. inversion H5.
    + subst. rewrite H in H10. discriminate.
    + subst. inversion H6. rewrite H in H10. rewrite H0 in H10. discriminate.
    + subst. assert (c = c0). eapply step_cost_is_unique; eauto.
      subst.
      assert (k = k0).
      apply IHmax_run_cost1.
      auto.
      subst.
      auto.
    + subst. assert (c = c0). eapply step_cost_is_unique; eauto.
      subst.
      assert (k' = k'1).
      apply IHmax_run_cost2.
      rewrite H in H9.
      inversion H9.
      subst.
      auto.
      subst.
      assert (k = k0).
      apply IHmax_run_cost1.
      auto.
      subst.
      omega.
  - intros. inversion H5.
    + subst. rewrite H in H10. discriminate.
    + subst. inversion H6.
      rewrite H in H10.
      rewrite H0 in H10.
      discriminate.
    + subst. rewrite H in H9. inversion H9.
      subst.
      assert (c = c0).
      eapply step_cost_is_unique; eauto.
      subst.
      assert (k = k0).
      apply IHmax_run_cost1.
      auto.
      subst.
      assert (k' = k'1).
      apply IHmax_run_cost2.
      auto.
      subst.
      omega.
    + subst.
      assert (c = c0).
      eapply step_cost_is_unique; eauto.
      subst.
      assert (k' = k'1).
      apply IHmax_run_cost2.
      rewrite H in H9. inversion H9.
      subst.
      auto.
      subst.
      auto.
Qed.


(* Some useful auxiliary lemmas ... *)

(** Erasure is reflexive **)
 Lemma LRefl : forall m, erased m m.
 Proof.
  intros.
  induction m.
  - econstructor.
  - destruct a.
    econstructor.
    auto.
Qed.

Lemma state_erased_refl : forall s, state_erased s s.
Proof.
  intros.
  destruct s as ((p,pc),m).
  - econstructor.
    apply LRefl.
Qed.

Lemma erased_trace_refl : forall r,  erased_trace r r.
  intros.
  induction r.
  - econstructor.
  - econstructor.
    apply state_erased_refl.
    auto.
Qed.

Lemma L0:  forall x v m1 m2, (erased m1 m2) -> (erased (assign_var x v m1) (assign_var x v m2)).
Proof.
  intros.
  induction H.
  - unfold assign.
    case (eq_var x x0).
    + econstructor; auto.
    + econstructor; auto.
  - unfold assign.
    case (eq_var x x0).
    + econstructor; auto.
    + econstructor; auto.
  - unfold assign.
    econstructor; econstructor; auto.
Qed.

Lemma L1:  forall x v m1 m2, (erased m1 m2) -> (erased (assign_var x v m1) (assign_var x None m2)).
Proof.
  intros.
  induction H.
  - unfold assign.
    case (eq_var x x0).
    + case v; econstructor; auto.
    + econstructor; auto.
  - unfold assign.
    case (eq_var x x0).
    + case v; econstructor; auto.
    + econstructor; auto.
  - unfold assign.
    case v; econstructor; econstructor; auto.
Qed.


Lemma L2:  forall x m1 m2, (erased m1 m2) -> (assoc_var x m1) = None -> (assoc_var x m2) = None.
Proof.
  intros.
  induction H.
  - revert H0.
    unfold assoc_opt.
    case (eq_var x x0); auto.
  - revert H0.
    unfold assoc_opt.
    case (eq_var x x0).
    + intro.
      inversion H0.
    + auto.
  - unfold assoc_opt.
    auto.
Qed.

Lemma L2bis:  forall x m1 m2, (erased m1 m2) -> (assoc_var x m2) = None -> (assoc_var x m1) = None.
Proof.
  intros.
  induction H.
  - revert H0.
    unfold assoc_opt.
    case (eq_var x x0); auto.
  - revert H0.
    unfold assoc_opt.
    case (eq_var x x0).
    + intro.
      inversion H0.
    + auto.
  - unfold assoc_opt.
    auto.
Qed.

Lemma L3:  forall x m1 m2, (erased m1 m2) -> (assoc_var x m1) ==? None -> (assoc_var x m2) ==? None.
Proof.
  intros.
  induction H.
  - revert H0.
    unfold assoc_opt.
    case (eq_var x x0); auto.
  -  revert H0.
     unfold assoc_opt.
     case (eq_var x x0); auto.
  - auto.
Qed.

Lemma L4:  forall x v1 v2 m1 m2, (erased m1 m2) -> (assoc_var x m1) ==? (Some v1) -> (assoc_var x m2) ==? (Some v2) -> v1 = v2.
Proof.
  intros.
  induction H.
  - revert H1.
    revert H0.
    unfold assoc_opt.
    case (eq_var x x0).
    + intros.
      inversion H0.
      inversion H1.
      subst.
      inversion H4; auto.
    + auto.
  - revert H0.
    revert H1.
    unfold assoc_opt.
    case (eq_var x x0).
    + intro.
      inversion H1.
    + auto.
  - revert H0.
    revert H1.
    unfold assoc_opt.
    intro.
    inversion H1.
Qed.

Lemma L5:  forall x v m1 m2, (erased m1 m2) -> (assoc_var x m2) = Some v -> exists w, (assoc_var x m1) = Some w.
Proof.
  intros.
  remember (assoc_opt eq_var x m1) as opt1.
  destruct opt1.
  - intros.
    econstructor.
    eauto.
  - symmetry in Heqopt1.
    eapply (L2 x m1 m2) in Heqopt1; auto.
    remember (assoc_opt eq_var x m1) as opt1.
    rewrite H0 in Heqopt1.
    inversion Heqopt1.
Qed.

Lemma L5bis:  forall x v m1 m2, (erased m1 m2) -> (assoc_var x m1) = Some v -> exists w, (assoc_var x m2) = Some w.
Proof.
  intros.
  remember (assoc_opt eq_var x m2) as opt2.
  destruct opt2.
  - intros.
    econstructor.
    eauto.
  - symmetry in Heqopt2.
    eapply (L2bis x m1 m2) in Heqopt2; auto.
    remember (assoc_opt eq_var x m1) as opt1.
    rewrite H0 in Heqopt2.
    inversion Heqopt2.
Qed.


(** The conservation property : if there is a transition s1 ~~> s2 in the non-deterministic semantics, there exists an equivalent transition s1' ~~> s2' with erased memories (ie. s1 --> s1' and s2 --> s2') **)
Lemma conservation : forall P pc1 pc2 M1 M2 M1' ,
    nondet_sem (P,pc1,M1) (P,pc2,M2) -> erased M1 M1' -> exists M2' , nondet_sem (P,pc1,M1') (P,pc2,M2') /\ erased M2 M2'.
Proof.
  intros.
  inversion H.
  - exists (assign eq_var x (Some n) M1').
    split.
    + eapply ND_Step_1; auto.
    + apply L0; auto.
  - assert (H7' := H7).
    eapply L5bis in H7'; eauto.
    destruct H7'.
    exists (assign eq_var x x0 M1').
    destruct w.
    + destruct x0.
      * assert (n = n0) by (eapply L4; eauto).
        subst.
        split.
        -- eapply ND_Step_2; eauto.
        -- apply L0; auto.
      * split.
        -- eapply ND_Step_2; eauto.
        -- apply L1; auto.
    + destruct x0.
      *  eapply L3 in H7; eauto.
         rewrite H7 in H8.
         inversion H8.
      * split.
        -- eapply ND_Step_2; eauto.
        -- apply L0; auto.
  - assert (H7' := H7).
    assert (H8' := H8).
    apply L5bis with (m2:=M1') in H7'.
    apply L5bis with (m2:=M1') in H8'.
    destruct H7'.
    destruct H8'.
    exists (assign eq_var x (lifted_plus x0 x1) M1').
    destruct v,w.
    + destruct x0,x1.
      -- assert (n=n1) by (eapply L4; eauto).
         assert (n0=n2) by (eapply L4; eauto).
         subst.
         split.
         --- eapply ND_Step_3; eauto.
         --- eapply L0; auto.
      -- split.
         --- eapply ND_Step_3; eauto.
         --- apply L1; auto.
     -- assert (n0=n1) by (eapply L4; eauto).
         subst.
         split.
        --- eapply ND_Step_3; eauto.
        --- simpl.
             apply L1; auto.

      -- split.
         --- eapply ND_Step_3; eauto.
         --- simpl.
             apply L1; auto.
    + destruct x1.
      -- eapply L3 in H8.
         rewrite H8 in H10.
         inversion H10.
         auto.
      -- destruct x0.
         ++ split.
            --- eapply ND_Step_3; eauto.
            --- simpl.
            apply L1; auto.
         ++ split.
            --- eapply ND_Step_3; eauto.
            --- simpl.
                apply L1; auto.

    + destruct x0.
      -- eapply L3 in H7.
         rewrite H7 in H9.
         inversion H9.
         auto.
      -- destruct x1.
         ++ split.
            --- eapply ND_Step_3; eauto.
            --- simpl.
                apply L1; auto.

         ++ split.
            --- eapply ND_Step_3; eauto.
            --- simpl. apply L1; auto.

    + destruct x0.
      -- eapply L3 in H7.
         rewrite H7 in H9.
         inversion H9.
         auto.
      -- destruct x1.
         ++ eapply L3 in H8.
         rewrite H8 in H10.
         inversion H10.
         auto.
         ++ split.
            --- eapply ND_Step_3; eauto.
            --- simpl.
                apply L0; auto.

    + auto.
    + auto.
  - assert (H7' := H7).
    assert (H8' := H8).
    apply L5bis with (m2:=M1') in H7'.
    apply L5bis with (m2:=M1') in H8'.
    destruct H7'.
    destruct H8'.
    exists (assign eq_var x (lifted_minus x0 x1) M1').
    destruct v.
    + destruct x0.
      -- destruct w.
         ++ destruct x1.
            assert (n1=n2) by (eapply L4; eauto).
            assert (n=n0) by (eapply L4; eauto).
            subst.
            split.
            --- eapply ND_Step_4; eauto.
            --- eapply L0. auto.
            --- split.
                eapply ND_Step_4; eauto.
                apply L1. auto.
         ++  destruct x1.
             assert (n=n0) by (eapply L4; eauto).
             eapply L3 in H8.
             rewrite H8 in H10.
             inversion H10.
             auto.
             split.
             eapply ND_Step_4; eauto.
             apply L1.
             auto.
      -- destruct w.
         ++ destruct x1.
            split.
            eapply ND_Step_4; eauto.
            apply L1.
            auto.
            split.
            eapply ND_Step_4; eauto.
            simpl.
            apply L1.
            auto.
         ++ destruct x1.
            eapply L3 in H8.
            rewrite H8 in H10. discriminate.
            auto.
            split.
            eapply ND_Step_4. eauto.
            auto.
            auto.
            eapply L1.
            auto.
    + destruct x0.
      -- eapply L3 in H7.
         rewrite H7 in H9.
         inversion H9.
         auto.
      -- destruct x1.
         ++ split.
            eapply ND_Step_4; eauto.
            apply L1.
            auto.
         ++ split.
            eapply ND_Step_4; eauto.
            simpl.
            apply L1.
            auto.
    + auto.
    + auto.
  - eexists.
    split.
    + subst.
      eapply ND_Step_5; auto.
    + subst.
      auto.
  - eexists.
    split.
    + subst.
      assert (H7' := H7).
      eapply L5bis in H7'; eauto.
      destruct H7'; eauto.
      destruct x0.
      * assert (0 = n0) by (eapply L4; eauto).
        subst.
        eapply ND_Step_6; eauto.
      * eapply ND_Step_8; eauto.
    + subst.
      auto.
  - eexists.
    split.
    + subst.
      assert (H7' := H7).
      eapply L5bis in H7'; eauto.
      destruct H7'; eauto.
      destruct x0.
      * assert ((S k) = n) by (eapply L4; eauto).
        subst.
        eapply ND_Step_7; eauto.
      * eapply ND_Step_9; eauto.
    + subst.
      auto.
  -  eexists.
    split.
    + subst.
      assert (H7' := H7).
      eapply L3 in H7'; eauto.
      eapply ND_Step_8; eauto.
    + subst. auto.
  -  eexists.
    split.
    + subst.
      assert (H7' := H7).
      eapply L3 in H7'; eauto.
      eapply ND_Step_9; eauto.
    + subst; auto.
Qed.

(** The conservations property holds when going from the deterministic semantics to the nondet :  **)
Lemma post_embedding_conservation : forall P pc1 pc2 M1 M2 M1' ,
    det_sem (P,pc1,M1) (P,pc2,M2) -> erased M1 M1' -> exists M2' , nondet_sem (P,pc1,M1') (P,pc2,M2') /\ erased M2 M2'.
Proof.
  intros.
  apply embedding in H.
  eapply conservation.
  eauto.
  auto.
Qed.

(** A trace in the non-deterministic semantics : **)
Inductive trace_nondet: list state -> Prop :=
| Trace_Nondet_1 : forall st,
    trace_nondet (st::nil)
| Trace_Nondet_2 : forall st1 st2 r,
    (nondet_sem st1 st2) ->
    trace_nondet (st2::r) ->
    trace_nondet (st1::st2::r).

(** A deterministic trace is a non-deterministic trace **)
Lemma trace_embedding : forall s T , run s T -> trace_nondet (T).
Proof.
  intros.
  induction H.
  - econstructor.
  - destruct r.
    + inversion IHrun.
    + econstructor.
      apply embedding.
      apply step_opt_det_sem.
      assert (st' = s).
      inversion H0.
      subst.
      auto.
      auto.
      subst.
      auto.
      auto.
Qed.


(** A program doesnt change after erasure of the memory of the state **)

Lemma program_invariant : forall p1 p2 pc1 pc2 m1 m2,
    nondet_sem (p1,pc1,m1) (p2,pc2,m2) -> p1 = p2.
Proof.
  intros.
  inversion H; auto.
Qed.

      (** Conservation property for nondet traces **)
Lemma trace_conservation : forall T  s s' ,
    trace_nondet (s::T) -> state_erased s s' -> exists T' , erased_trace  (s::T) (s'::T') /\ trace_nondet(s'::T').
Proof.
  intros T.
  induction T.
  - intros. inversion H.
    exists nil.
    econstructor.
    + econstructor. auto.
      econstructor.
    + econstructor.
  - intros.
    inversion H0.
    inversion H.
    subst.
    destruct a.
    destruct p0.
    assert (H6' := H6).
    apply program_invariant in H6'; subst.
    eapply conservation in H6; eauto.
    destruct H6.
    destruct H2.
    assert (state_erased (l0, n, l) (l0, n, x)) by (econstructor; auto).
    eapply IHT in H8; eauto.
    destruct H8.
    destruct H5.
    econstructor.
    econstructor.
    + econstructor; eauto.
    + econstructor; eauto.
Qed.


Lemma post_embedding_trace_conservation : forall T s s' ,
    run s (s::T) -> state_erased s s' -> exists T', erased_trace (s::T) (s'::T') /\ trace_nondet (s'::T').
Proof.
  intros.
  apply trace_conservation.
  apply trace_embedding in H.
  auto.
  auto.
Qed.


Lemma post_embedding_trace_conservation' : forall T s ,
    run s (T) -> exists T', erased_trace (T) (T') /\ trace_nondet (T').
Proof.
  intros.
  destruct T.
  - inversion H.
  -
    assert (H':=H).
    apply run_init in H.
    subst.
    assert (H'':=H').
    eapply post_embedding_trace_conservation in H'.
    destruct H'.
    destruct H.
    eexists.
    split.
    eauto.
    eauto.
    apply state_erased_refl.
Qed.

(** The final function returns True if the given state is final (i.e. is a Return instr) **)

Definition final (st : option state) :=
  match st with
  | None => False
  | Some (p, pc, m) => assoc_instr pc p ==? Return
  end.

(** The last function returns the last state of a trace :  **)

Fixpoint last {A} (l : list A) :=
  match l with
  | nil => None
  | (h :: nil) => Some h
  | (h :: t) => last t
  end.

(** last doesnt care about the head of a trace : **)

Lemma last_cons : forall st (r : list state) , r <> nil -> last(st :: r) = last (r).
Proof.
  intros.
  induction r.
  - contradiction.
  - simpl.
    destruct r.
    auto.
    auto.
Qed.

(** A normal trace is a trace that ends with a Return instruction :  **)

Definition trace_norm (T : list state) := final(last(T)).

(** A finite trace is a trace that follows the non deterministic semantics and
  ends with a return instruction :  **)

Definition trace_finite (T : list state) := final(last(T)) /\ trace_nondet(T).


(** Obvious lemmas  : **)

Lemma trace_finite_is_trace_nondet : forall T, trace_finite T -> trace_nondet T.
  intros.
  destruct H.
  auto.
Qed.

Lemma erased_trace_same_length : forall T T', erased_trace T T' -> length T = length T'.
  intros.
  induction H.
  - auto.
  - simpl.
    auto.
Qed.

Lemma trace_nondet_cons : forall T s , T <> nil -> trace_nondet (s::T) -> trace_nondet T.
  intros.
  induction T.
  - destruct H.
    auto.
  - inversion H0.
    subst.
    auto.
Qed.


Lemma nondet_erased_is_nondet : forall s1 s1' s2 ,
    nondet_sem s1 s2 -> state_erased s1 s1' -> exists s2',  nondet_sem s1' s2'.
Proof.
  intros.
  destruct s1 as ((p,pc),m).
  destruct s2 as ((p',pc'),m').
  assert (p = p').
  apply program_invariant in H.
  auto. subst.
  destruct s1' as ((p'',pc''),m'').
  inversion H0.
  subst.
  eapply conservation in H.
  inversion H.
  inversion H1.
  eexists.
  eauto.
  eauto.
Qed.


Lemma trace_finite_is_normal : forall T , trace_finite T -> final(last(T)).
  intros.
  destruct H.
  auto.
Qed.

(** A deterministic run finishes with the return instruction, it is thus normal  : **)

Lemma deterministic_is_normal : forall s T ,
    run s T -> final (last (T)).
Proof.
  Proof.
    intros.
    induction H.
    - simpl. auto.
    - rewrite last_cons.
      auto.
      destruct r.
      inversion IHrun.
      discriminate.
  Qed.

(** Because the deterministic semantics can be lifted to the non deterministic semantics,
   a deterministic run is a finite run  **)

Lemma deterministic_is_finite : forall s T,
    run s T -> trace_finite T.
Proof.
  Proof.
    intros.
    unfold trace_finite.
    split.
    eapply deterministic_is_normal.
    eauto.
    eapply trace_embedding.
    eauto.
  Qed.

(** A normal run stays normal after erasure of its memory **)
  Lemma erased_norm_is_norm_aux: forall t t',
      erased_trace t t' ->
      final (last (t)) ->
      final (last (t')).
  Proof. intros.
         induction H.
         - auto .
         - inversion H.
           inversion H1.
           + subst.
             inversion H.
             subst.
             simpl in H0.
             simpl. auto.
           + subst.
             rewrite last_cons in H0.
             rewrite last_cons.
             apply IHerased_trace.
             auto.
             discriminate.
             discriminate.
  Qed.

  Lemma erased_norm_is_norm : forall r,
      final(last(r)) -> forall r', erased_trace r r' -> final (last(r')).
  Proof.
    intros.
    eapply erased_norm_is_norm_aux.
    eauto.
    auto.
  Qed.


    (** The max run is very close to max run cost but returns the trace of the maximum run of
 the program, not its cost **)

  Inductive max_run: state -> (list state) -> Prop :=
| Max_Run_1 : forall p pc m, (* final state *)
    assoc_instr pc p ==? Return ->
    max_run (p, pc, m) ((p, pc, m) :: nil)
| Max_Run_2 : forall st st' r,
    step_opt st ==? st' ->
    max_run st' r ->
    max_run st (st::r)
| Max_Run_3 : forall p pc m x n r r', (* non-deterministic rules *)
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? None ->
    max_run (p, pc + 1, m) r ->
    max_run (p, n, m) r' ->
    cost r > cost r' ->
    max_run (p, pc, m) ((p, pc, m) :: r)
| Max_Run_4 : forall p pc m x n r r',
    assoc_instr pc p ==? (Branchif x n) ->
    assoc_var x m ==? None ->
    max_run (p, pc + 1, m) r ->
    max_run (p, n, m) r' ->
    cost r <= cost r' ->
    max_run (p, pc, m) ((p, pc, m) :: r')
.


(** Useful property : a max run always begins with its the state given as a first parameter : **)

Lemma max_run_init : forall s s' T , max_run s (s' :: T) -> s = s'.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

(** A max run is a special case of finite run :  **)
Lemma max_run_is_finite : forall s T , max_run s T -> trace_finite T.
Proof.
  intros.
  induction H.
  - econstructor. simpl. auto.
    econstructor.
  - econstructor.
    inversion IHmax_run.
    +
      rewrite last_cons.
      auto.
      destruct r.
    -- simpl in H1. inversion H1.
    -- discriminate.
    + inversion IHmax_run.
      inversion H2.
      subst.
      econstructor.
      assert (H0':= H0).
      apply max_run_init in H0.
      subst.
      apply step_opt_det_sem in H.
      apply embedding in H.
      auto.
      auto.
      subst.
      econstructor.
      apply max_run_init in H0.
      subst.
      apply step_opt_det_sem in H.
      apply embedding in H.
      auto.
      auto.
  - split.
    +
    inversion IHmax_run1.
    ++ rewrite last_cons.
    auto.
    destruct r.
      -- inversion H5.
      -- discriminate.
    + destruct r.
      inversion H3.
      -- econstructor.
         inversion H1.
         ++ subst.
            econstructor 8.
            eauto.
            auto.
         ++ econstructor 8.
            eauto.
            auto.
         ++ econstructor 8.
            eauto.
            auto.
         ++ econstructor 8.
            eauto.
            auto.
         ++ unfold trace_finite in IHmax_run1.
            destruct IHmax_run1.
            auto.
  - split.
    +
      unfold trace_finite in IHmax_run2.
      destruct IHmax_run2.
      rewrite last_cons.
      auto.
      destruct r'.
      inversion H4.
      discriminate.
    + destruct r'.
      -- econstructor.
      -- econstructor.
         inversion H2; subst.
        ++  econstructor 9.
            eauto.
            auto.
         ++ econstructor 9.
            eauto.
            auto.
         ++ econstructor 9.
            eauto.
            auto.
         ++ econstructor 9.
            eauto.
            auto.
         ++ unfold trace_finite in IHmax_run2.
            destruct IHmax_run2.
            auto.
Qed.



(** Quite obviously, the cost of the max run is the maximum cost of the program :  **)
Lemma max_run_cost_is_max_cost: forall st k, max_run_cost st k -> exists r, max_run st r /\ cost r = k.
Proof.
  intros st k H.
  induction H.
  - eexists.
    split.
    econstructor.
    auto.
    simpl.
    rewrite H.
    auto.
  - inversion IHmax_run_cost.
    destruct H2.
    eexists.
    split.
    econstructor.
    eauto.
    eauto.
    simpl.
    rewrite H0.
    subst.
    auto.
  - inversion IHmax_run_cost2.
    inversion IHmax_run_cost1.
    destruct H5.
    destruct H6.
    eexists.
    split.
    eapply Max_Run_3.
    eauto.
    auto.
    eauto.
    eauto.
    rewrite H8.
    rewrite H7.
    auto.
    simpl.
    rewrite H.
    rewrite H8.
    inversion H1.
    rewrite H in H10.
    inversion H10.
    subst.
    auto.
  - inversion IHmax_run_cost2.
    inversion IHmax_run_cost1.
    destruct H5.
    destruct H6.
    eexists.
    split.
    eapply Max_Run_4.
    eauto.
    auto.
    eauto.
    eauto.
    rewrite H8.
    rewrite H7.
    auto.
    simpl.
    rewrite H.
    rewrite H7.
    inversion H1.
    rewrite H in H10.
    inversion H10.
    subst.
    auto.
Qed.

(** Some useful lemmas **)

Lemma L10: forall (st: state) r, cost (st :: r) >= cost (st :: nil).
Proof.
  intros.
  simpl; auto.
  case (step_cost st).
  - intros.
    omega.
  - omega.
Qed.

Lemma L11: forall (st: state) r r',  cost r >= cost r' -> cost (st :: r) >= cost (st :: r').
Proof.
  intros.
  simpl; auto.
  case (step_cost st).
  - intros.
    omega.
  - omega.
Qed.

(** The max run is finite, thus it is normal :  **)
Lemma max_run_is_normal : forall s T , max_run s T -> final(last(T)).
Proof.
  intros.
  apply max_run_is_finite in H.
  destruct H.
  auto.
Qed.


(** Auxiliary lemmas **)
Lemma max_run_init2 : forall s t , max_run s t -> exists t' , t = s::t'.
  intros.
  inversion H; eexists; eauto.
Qed.

Lemma nondet_det_equals : forall s s' s'' , nondet_sem s s' -> step_opt s ==? s'' -> s' = s''.
Proof.
  intros.
  induction H.
  - simpl in H0. rewrite H in H0. inversion H0. auto.
  - simpl in H0. rewrite H in H0. rewrite H1 in H0. inversion H0. auto.
  - simpl in H0. rewrite H in H0. rewrite H1 in H0. rewrite H2 in H0. inversion H0. auto.
  - simpl in H0. rewrite H in H0. rewrite H1 in H0. rewrite H2 in H0. inversion H0. auto.
  - simpl in H0. rewrite H in H0. inversion H0. auto.
  - simpl in H0. rewrite H in H0. rewrite H1 in H0. simpl in H0. inversion H0. auto.
  - simpl in H0. rewrite H in H0. rewrite H1 in H0. simpl in H0. inversion H0. auto.
  - simpl in H0. rewrite H in H0. rewrite H1 in H0. inversion H0.
  - simpl in H0. rewrite H in H0. rewrite H1 in H0. inversion H0.
Qed.



(** The max run has a cost that is greater than all the others finite traces :  **)
Lemma max_run_is_max : forall st r, trace_finite (st::r) -> forall r', max_run st (r') -> (cost (r') >= cost (st::r)).
Proof.
  intros.
  unfold trace_finite in H.
  destruct H.
  generalize dependent r.
  induction H0.
  - intros. inversion H1.
    + subst.
      auto.
    + apply L11.
      subst.
      inversion H4; subst.
      rewrite H in H8. discriminate.
      rewrite H in H8. discriminate.
      rewrite H in H7. discriminate.
      rewrite H in H7. discriminate.
      rewrite H in H8. discriminate.
      rewrite H in H8. discriminate.
      rewrite H in H8. discriminate.
      rewrite H in H8. discriminate.
      rewrite H in H8. discriminate.
  - intros.
    inversion H2.
    + subst.
    apply L11.
    simpl.
    omega.
    + subst.
      apply L11.
      assert (st2 = st').
      eapply nondet_det_equals.
      eauto.
      eauto.
      subst.
      apply IHmax_run.
      rewrite last_cons in H1.
      auto.
      discriminate.
      auto.
  - intros.
    inversion H3.
    + subst.
    apply L11.
    simpl.
    omega.
    + subst.
      apply L11.
      inversion H6; subst.
      -- rewrite H in H10. discriminate.
      -- rewrite H in H10. discriminate.
      -- rewrite H in H9. discriminate.
      -- rewrite H in H9. discriminate.
      -- rewrite H in H10. discriminate.
      -- rewrite H in H10. inversion H10.
         subst.
         rewrite H0 in H11. discriminate.
      -- rewrite H in H10. inversion H10.
         subst.
         rewrite H0 in H11. discriminate.
      -- rewrite H in H10. inversion H10.
         subst.
         apply IHmax_run1.
         rewrite last_cons in H2.
         auto.
         discriminate.
         auto.
      -- rewrite H in H10. inversion H10.
         subst.
         clear H10 H11.
         rewrite last_cons in H2.
         assert (final(last ((p,n0,m)::r1))).
         auto.
         apply IHmax_run2 in H4.
         omega.
         auto.
         discriminate.
  -  intros.
    inversion H3.
    + subst.
    apply L11.
    simpl.
    omega.
    + subst.
      apply L11.
      inversion H6; subst.
      -- rewrite H in H10. discriminate.
      -- rewrite H in H10. discriminate.
      -- rewrite H in H9. discriminate.
      -- rewrite H in H9. discriminate.
      -- rewrite H in H10. discriminate.
      -- rewrite H in H10. inversion H10.
         subst.
         rewrite H0 in H11. discriminate.
      -- rewrite H in H10. inversion H10.
         subst.
         rewrite H0 in H11. discriminate.
      -- rewrite H in H10. inversion H10.
         subst.
         clear H10 H11.
         rewrite last_cons in H2.
         assert (final(last ((p,pc+1,m)::r1))).
         auto.
         apply IHmax_run1 in H4.
         omega.
         auto. discriminate.
      -- rewrite H in H10. inversion H10.
         subst.
         apply IHmax_run2.
         rewrite last_cons in H2.
         auto.
         discriminate.
         auto.
Qed.


(** The cost of the max run is still greater than other finite traces even when its computed
  from an erased version of the memories of the traces **)
Lemma max_run_erased :
  forall m st', max_run st' m ->
                forall st r, trace_finite (st :: r) ->
                             forall r', trace_finite (st' :: r') ->
                                        erased_trace (st :: r) (st' :: r') ->
                                        cost m >= cost (st :: r).
Proof.
  intros.
  eapply trace_cost_erased_is_equal in H2.
  eapply max_run_is_max in H; try eapply H1.
  omega.
Qed.

(** The cost of the max run is greater than other finite traces even when its computed
  from an erased version of the memory of the beginning state **)

Lemma max_run_erased_is_max :
  forall m st', max_run st' m ->
                forall st r, trace_finite  (st::r) ->
                             state_erased st st' ->
                             cost m >= cost (st::r).
Proof.
  intros.
  assert (H10:=H0).
  eapply trace_finite_is_trace_nondet in H10.
  assert (H11:=H0).
  eapply trace_finite_is_normal in H11.
  eapply trace_conservation in H10; eauto.
  destruct H10.
  destruct H2.
  eapply erased_norm_is_norm in H11; eauto.
  eapply max_run_erased;
  eauto.
  split.
  auto.
  auto.
Qed.


(** The cost computed by max run cost from an erased version of the memory of the beginning state
  is greater than the cost of every finite trace **)
Lemma max_run_erased_is_max_cost :
  forall k st', max_run_cost st' k ->
                forall st r, trace_finite (st::r) ->
                             state_erased st st' ->
                             k >= cost (st::r).
Proof.
  intros.
  eapply max_run_cost_is_max_cost in H.
  destruct H.
  destruct H.
  subst.
  eapply max_run_erased_is_max ; eauto.
Qed.



(** The cost computed by max run cost from an erased version of the memory of the beginning state
  is greater than the actuel cost of the program **)
Theorem max_cost_final :
  forall k st', max_run_cost st' k ->
                forall st r, run st (st::r) ->
                             state_erased st st' ->
                             k >= cost (st::r).
Proof.
  intros.
  eapply deterministic_is_finite in H0.
  eapply max_run_erased_is_max_cost.
    eauto.
    auto.
    auto.
Qed.


(** The final theorem : k is an upper bound of the cost of the actual execution of the program **)
Theorem max_cost_final' :
  forall k st', max_run_cost st' k ->
                forall st r, run st (r) ->
                             state_erased st st' ->
                             k >= cost (r).
Proof.
  intros.
  destruct r.
  simpl. omega.
  assert (H0':=H0).
  apply run_init in H0.
  subst.
  eapply max_cost_final.
    eauto.
    auto.
    auto.
Qed.


(** The theorem as it is shown in the manuscript : **)

Theorem max_cost_final_rephrased :
  forall k st st' t,
    run st (t) ->
    state_erased st st' ->
    max_run_cost st' k ->
    k >= cost (t).
Proof.
  intros.
  eapply max_cost_final'; eauto.
Qed.


(* QED *)
