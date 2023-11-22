(* Time-stamp: <Mon 7/3/23 17:33 Dan Dougherty Iteration.v>

1. Worked out for the easy case when termination is by a nat-valued
measure functon.

Easy enough to generalized to the wellFounded case

2. The second part, specifying to the case where the function being
iterated is derived from a conditional function gen : X -> X + E, is
also simplified, since E in particular has no structure.  The really
interesting case is when X+E is a sumor, so that the having [ gen x ]
landing in E means we get an assertion about [x].  What's here is a
template for how to go about doing all that, from scrtach.

*)

From Coq Require Import List. Export ListNotations.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Morphisms .
From Coq Require Import RelationClasses .
From Coq Require Import Setoid .
From Coq Require Import FunInd.
From Coq Require Import Recdef.
From Coq Require Export Logic.FunctionalExtensionality.
From Coq Require Export Lia.
From Coq Require Import Program.
From Coq Require Import FunInd.
From Coq Require Import Recdef.
From Equations Require Import Equations.

From RC Require Import Decidability.

(* just in case *)
Unset Implicit Arguments.


(** * A General Iteration Combinator  *)
(* ================================== *)

Section LoopBasic.

Context { X: Type }.
Variable f : X -> X.

Definition fixed (x : X) : Prop := f x = x.

Equations loop (n: nat) (x : X) : X :=
  loop 0 x  := x;
  loop (S m) x  := f  (loop  m x).

(** Adapted from [FunctionalElimination_loop] *)
Lemma loopElim  :
  (forall P : nat -> X -> X -> Type,
      (forall x : X, P 0 x x)
      -> (forall (m : nat) (x : X), 
             P m x (loop m x) -> 
             P (S m) x (f (loop m x)))
      -> forall (n : nat) (x : X), P n x (loop n x)).
Proof.
  intros P H0 H1 n x.
  induction n as [| n' IH].
  - rewrite (loop_equation_1); apply H0.
  - apply H1. apply IH.
Qed.

 
Lemma loop_fixed x n :
  fixed x -> fixed (loop n x).
Proof.
 unfold fixed; intros;
  induction n as [| n' IH]; auto;
  simp loop; rewrite IH; easy.
Qed.   

(** ** Adding a measure *)

Variable m : X -> nat.

(*
Note that we don't ask that [m (f x) > m x] for all [x]; only for
non-fixed [x] *)

Definition decreasing : Prop :=
  forall x, fixed x \/ m (f x) < m x.  

Lemma loop_decreasing :
  decreasing  ->
  forall x n, 
  fixed (loop n x) \/ 
    ( m (loop (S n) x) < m (loop n x) ).
Proof.
intros H x n;  simp loop; auto.
Qed.

Lemma loop_decreasing_strong :
  decreasing  ->
  forall x n, 
  fixed (loop n x) \/ 
    ( n + m (loop n x)  <= m x ).
Proof.
  intros H x n.
  induction n; simpl.
  - auto. 
  - destruct IHn as [L|R].
    + left. now rewrite L. 
    + 
      (* unfold decreasing in H . *)
      destruct (H (loop n x)) as [Fx | Lt].
      * left. simp loop. now rewrite Fx.   
      * right.  simp loop.  lia.
Qed.

(** ** Computing a fixed point *)

(* Spose we have a [m] function on [X] such that all [x] not fixed by
[f] have their [m] go down after [f].

Then iterating on [x] for [m x] steps gives a fixed point.
*)

Definition max_loop (x: X) :=
   (loop (m x) x).

Theorem fixed_max_loop :
  decreasing ->
  forall x, fixed (max_loop x). 
Proof.
  intros SD x.
  assert (a:= loop_decreasing SD x (m x)).
  destruct a;
    destruct (loop_decreasing_strong SD x (m x)); auto; exfalso; lia.
Qed.

End LoopBasic.

Arguments loop {X}.


(* ============================================ *)
(** ** Reasoning About Iteration *)
(* ============================================ *)

(** *** Proofs about binary relations *)
Section Binary_Proofs.
  
  (** Suppose we want to prove that a relation R  holds between [x] and any [loop f n x].

Here is a proof, provided

- R is reflexive and transitive
- R holds between each [x] and [f x].
   *)
  
  Variable X: Type.
  Variable f: X -> X.
  Variable R : X -> X -> Prop.

  Hypothesis Href: reflexive _ R. 
  Hypothesis Htrans : transitive _ R.
  Hypothesis Hf : forall x, R x (f x).

  Theorem pre_post : forall x n, R x (loop f n x).
  Proof.
    intros x n.
    apply (loopElim).
    - intros s. apply Href.
    - intros m s H. 
      apply Htrans with (loop f m s).
      + easy.
      + apply Hf.
  Qed.

End Binary_Proofs.

Arguments pre_post {X} {f} R _ _ _ _ _ .

(** *** Proofs about unary relations *)
Section Unary_Proofs.
  
  (** Suppose we want to prove a property P holds at each [loop f n x].

Here is a proof, provided

- P  holds at the start
- whenever P holds of x then P holds of [f x].

We reduce the problem to the previous one, defining the binary predicate
[R x y := Px -> Py]

   *)

  Variable X: Type.
  Variable f: X -> X.

  Variable P : X -> Prop.
  Hypothesis Hf : forall x, P x -> P (f x).

  Variable x0 : X.
  Hypothesis Hinit: P x0.

  Definition R (x y : X) : Prop :=
    P x -> P y.

  Lemma Rref: reflexive _ R.
  Proof. 
    unfold reflexive, R; auto.
  Qed.

  Lemma Rtrans : transitive _ R.
  Proof. 
    unfold transitive, R; intros; tauto.
  Qed.  

  Theorem prove_invariant : forall n, P (loop f n x0).
  Proof.
    intros n.
    assert (a:= pre_post R Rref Rtrans Hf x0 n). 
    unfold R in a. auto.
  Qed.

End Unary_Proofs. 
(* Check prove_invariant. *)
Arguments prove_invariant {X} {f} P  _ _ _ _  .


(* ============================== *)

(** A typical scenario : we have a [gen] function on x:[X] that either
    returns something "smaller" than [x] or an "error" value.

    We convert this into a step function : X -> X which is either
decreasing or fixed.  *)

Section Peeking.
  
  Context {X E: Type}.
  Variable gen : X -> X + E.
  
  Definition step (x : X)  : X :=
    match (gen x)  with
    | inl x' => x'
    | inr _ => x
    end.
  
  Lemma gen_left_step (x x': X) :
    gen x = inl x' -> 
    step x = x'.
  Proof.
    intros H;
      unfold step;
      rewrite H; easy.
  Qed.
  
  Lemma gen_right_step (x: X) (e: E) :
    gen x = inr e -> 
    step x = x.
  Proof.
    intros H;
      unfold step;
      rewrite H; easy.
  Qed.
  
  Definition steps (n: nat) (x: X) : X :=
    loop step n x.
  
  Variable m : X -> nat.
  
  Hypothesis gen_decreasing :
    forall x y, gen x = inl y ->
                m y < m x.
  
  
  (** If something is a fixed point of step then gen gives the "error"
      value *)
  
  Lemma fixed_goes_right1 x :
    step x = x ->
    exists e, gen (step x) = inr e.
  Proof.
    intros H; destruct (gen (step x)) eqn:e.
    - assert (h: step x = x0).
      { unfold step. rewrite <- H. now rewrite e. }
      assert (a:= gen_decreasing (step x) x0 e). subst. lia.
      
    - exists e0; easy.
  Qed.
  
  Lemma fixed_goes_right2 x :
    step x = x ->
    exists e, gen x = inr e.
  Proof.
    intros  H.
    assert (a:= fixed_goes_right1 x H).
    now rewrite H in a.
  Qed.
  
  Lemma step_decreasing :
    forall x, step x = x \/ m (step x) < m x.  
  Proof.
    intros x;  assert (a:= fixed_goes_right2 x).
    destruct (gen x) eqn:e ;
      unfold step; rewrite e; auto.
  Qed.
  
(** Now we can apply all the results in the first section, where the
[f] there is [step] *)
  
End Peeking.

Global Hint Unfold decreasing : core.
Global Hint Resolve gen_left_step : core.
Global Hint Resolve gen_right_step : core.

(* **************************************************** *)

(** * WellFounded Iteration *)

Section WfIteration.

  Variable X: Type.

  (** Assume a wellFounded ordering of X *)

  Variable lt_X: X -> X  -> Prop.
  Hypothesis irreflexive_lt_s :
    forall (s: X), lt_X s s -> False.
  Hypothesis transitive_lt_s :
    forall s1 s2 s3,
      lt_X s1 s2 ->
      lt_X s2 s3 ->
      lt_X s1 s3.
  Hypothesis wf_lt_X : well_founded lt_X.

  #[export] Instance wellfounded_lt_X : WellFounded lt_X := wf_lt_X .
  
  (** Computation step *)

  Variable step :  X -> X.
  
  (** Stopping condition *)

  Variable alldone: X -> Prop.
  
  (* What we need to assume about stopping condition *)

  Hypothesis alldone_dec: 
    forall (x:X), Decision (alldone x).
  
  Hypothesis alldone_fixed :
    forall (s: X), alldone s  -> step s = s.
  
  Hypothesis step_decreases : 
    forall (s: X), ~ alldone s  ->  lt_X (step s) s.
  
  (* ========================================= *)

  (** Main Definition *)
  Equations wfiter (s: X) : X
    by wf s lt_X :=
    wfiter s := if (decide (alldone s))
                then s
                else wfiter (step s)
  . 

  (* ========================================= *)

  (** ** Fixedpoint property of [wfiter] *)

  Theorem wfiter_fixed (s: X) :
    (step (wfiter s))  =   (wfiter s) .
  Proof.
    apply FunctionalElimination_wfiter.
    intros s0 H.
    assert (a:= alldone_fixed s0).
    decide_t (alldone s0); auto.
  Qed.

  (* ================================================== *)
  (** ** A General Template for Invariance Proofs *)

  Section Invariance_Proofs.

    Section Binary.
      Variable R : X -> X -> Prop.

      (* A binary predicate holds betwen [s] and [wfiter s] if
     
        - R is reflexive and transitive
        - R holds between any [s] and [step s].
       *)
            
      Hypothesis Href: forall sys, R sys sys.
      Hypothesis Htrans : forall sys1 sys2 sys3, 
          R sys1 sys2 -> R sys2 sys3 -> R sys1 sys3.
      Hypothesis Hstep : forall sys, R sys (step sys).

      Theorem wfiter_binary : forall sys, R sys (wfiter sys).
      Proof using Href Hstep Htrans.
        intros sys.
        apply FunctionalElimination_wfiter.
        intros sys0 H.
        - decide_t (alldone sys0).
          + apply Href.
          + specialize (H n).
            apply Htrans with (step sys0).
            apply Hstep.
            apply H.
      Qed.        

    End Binary.

    Section Unary.
      (** A unary predicate holds of [wfiter s]
    whenever it holds of [s] and is preserved by [step]
    
    Proof is by reducing this to the binary predicate 
    [R x y := Inv x -> Inv y] 

       *)
      Variable Inv : X -> Prop.
      Hypothesis Invstep : forall sys, Inv sys -> Inv (step sys).
      
      Theorem wfiter_invariant :
        forall s, Inv s -> Inv (wfiter s).
      Proof using Invstep.
        intros s H.
        apply (wfiter_binary (fun x y => Inv x -> Inv y));
          firstorder.
      Qed.
      
    End Unary.
    
  End Invariance_Proofs.
  
End WfIteration.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Section NatWfiteration.

  Variable X: Type.

  (** Computation on [X]   *)

  Variable step :  X -> X.

  Function nat_wfiter (n: nat) (s: X) : X :=
    match n with 
      0 => s
    | S m =>  step (nat_wfiter m s)
    end. 

  (** An induction priciple for wfiteration *)
  
Lemma wfiterate_ind (p : X -> Prop) x n :
    p x -> (forall (z: X), p z -> p (step z)) -> p (nat_wfiter n x).
  Proof .
    intros A B. induction n; simpl; auto.
  Qed.

  Definition step_fixed (x : X) : Prop := step x = x.

  (** ** Fixed point property *)
 
  (** A general version not using Decidability of X *)

  Theorem nat_wfiter_fixed' (measure : X -> nat) x :
    (forall n, step_fixed (nat_wfiter n x) \/ 
                 measure (nat_wfiter n x) > measure (nat_wfiter (S n) x)) ->
    step_fixed (nat_wfiter (measure x) x).
  Proof using Type.
    intros A.

    assert (B: forall n, 
               step_fixed (nat_wfiter n x) \/ 
                 measure x >= n + measure (nat_wfiter n x)).
    { intros n; induction n; simpl.
      - auto. 
      - destruct IHn as [B|B].
        + left. now rewrite B. 
        + destruct (A n) as [C|C].
          * left. now rewrite C. 
          * right. simpl in C. lia. }

    destruct (A (measure x)), (B (measure x)); auto; exfalso; lia.
  Qed.

  (** Most convenient phrasing uses decidability of X *)

  Lemma DN_imp  (x y : X) (p: Prop) `{eq_dec: EqDecision X} `{p_dec : Decision p} :
    (x <> y -> p) -> (x = y) \/ p.
  Proof.
    intros H.
    destruct (decide (x=y)) eqn: e; tauto. 
  Qed.

  (** If for every [n], applying a step to 
        [nat_wfiter n x] (if it's not itself a fixed point)
        makes the measure go down, then applying 
        [measure x] steps at [x] makes a fixed point.    *)

  Theorem nat_wfiter_fixed `{eq_dec: EqDecision X} (measure : X -> nat) x :
    (forall n, (~ step_fixed (nat_wfiter n x)) ->
               measure (nat_wfiter n x) > measure (nat_wfiter (S n) x)) ->
    step_fixed (nat_wfiter (measure x) x).
  Proof.
    intros H.
    apply nat_wfiter_fixed'.
    intros n.
    specialize (H n).
    unfold step_fixed in *.
    apply DN_imp. easy.
    destruct (gt_dec (measure (nat_wfiter n x))
                (measure (nat_wfiter (S n) x))) eqn:e.
    auto. auto. auto.
  Qed.
  
  
End NatWfiteration.

Arguments nat_wfiter {X} _ _  _. 

Arguments wfiter {X} _ _ _ _ _ . 


