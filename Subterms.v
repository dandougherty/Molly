 (* Time-stamp: <Thu 5/25/23 12:47 Dan Dougherty Subterms.v> *)

From Coq Require Import FunInd Nat Bool DecBool String List.
Import ListNotations.

From RC Require Export
  Utilities
  Sorts
  Term
  ListUtil
  CpdtTactics
.


(* =========================================== *)
(** * Subterm Predicates: [subtermP] and friends *)


(** ** Immediate Subterm *)
Inductive imm_subtermP : Term -> Term -> Prop :=
   imm_subtermP_pr1 : forall t1 t2 : Term,
      imm_subtermP t1 (Pr t1 t2)
| imm_subtermP_pr2 : forall t1 t2 : Term,
    imm_subtermP t2 (Pr t1 t2)
| imm_subtermP_en1 : forall t1 t2 : Term,
    imm_subtermP t1 (En t1 t2)
| imm_subtermP_en2 : forall t1 t2 : Term,
    imm_subtermP t2 (En t1 t2)
| imm_subtermP_hs : forall t1 : Term, imm_subtermP t1 (Hs t1).
#[export] Hint Constructors imm_subtermP : core.

(** TODO: [well_founded imm_subterm] *)

(* -- *)
 
(** ** STRICT subterm here *)
Inductive ssubtermP (x: Term) : Term -> Prop :=
| ssubtermP_dir (y:Term) : imm_subtermP x y -> ssubtermP x y
| ssubtermP_trans (y z:Term) : ssubtermP x y -> ssubtermP y z -> ssubtermP x z.
#[export] Hint Constructors ssubtermP : core.

(** TODO: [well_founded ssubterm] *)

(* -- *)

(** ** Strict-or-Equal. *) 
Inductive subtermP (x: Term) : Term -> Prop :=
| subtermP_refl : subtermP x x
| subtermP_dir (y:Term) : imm_subtermP x y -> subtermP x y
| subtermP_trans (y z:Term) : subtermP x y -> subtermP y z -> subtermP x z.
#[export] Hint Constructors subtermP : core.

(* ------------------------------------------- *)
(** * Subterms as a List: [subterms] *)

Fixpoint subterms (t: Term) : set Term :=
    (match t with
  | Pr t1 t2 => t :: (subterms t1) ++ (subterms t2)
  | En t1 t2 => t :: (subterms t1) ++ (subterms t2)
  | Hs t1 =>    t :: (subterms t1) 
  | _ => [t]
  end).
 
Lemma in_subterms t :
  In t (subterms t).
Proof.
  destruct t eqn:et; 
    simpl; auto.
Qed.
#[export] Hint Resolve in_subterms : core.

(** [subterm_closed] means closed under taking subtertms *)
Definition subterm_closed (u: set Term) :=
  forall (x: Term), In x u -> subterms x <<= u.

(* @@ crush slow here *)
Lemma subterms_subterm_closed (t: Term) :
  subterm_closed (subterms t).
Proof.
  intros x H.
  induction t; simpl; auto.

  9:{ destruct H; 
      subst;   auto;
      apply in_app_or in H; destruct H; auto. }
  
  9:{ destruct H; 
      subst;   auto;
      apply in_app_or in H; destruct H; auto. }

  all: simpl in H; inv H; simpl; now auto.
Qed.

Corollary subterms_trans x y z :
  In x (subterms y) ->
  In y (subterms z) ->
  In x (subterms z).
Proof.
  intros H1 H2.
  assert (a:= subterms_subterm_closed).
  specialize (a z y H2);  auto.
Qed.

Lemma subterms_dir_subterm x t :
  imm_subtermP x t -> 
  In x (subterms t) .
Proof.
  intros H.  inv H; simpl.
  - right. apply in_or_app. left. apply in_subterms.
  - right. apply in_or_app. right. apply in_subterms.
  - right. apply in_or_app. left. apply in_subterms.
  - right. apply in_or_app. right. apply in_subterms.
  - right. apply in_subterms.
Qed.
#[export] Hint Resolve subterms_dir_subterm : core.
(* ------------------------------------------- *)
(** * Lift [subterms] to subterms of a set : [Subterms] *)

Fixpoint Subterms (T: set Term) : set Term :=
  match T with 
    [] => empty_set 
  | t :: rest => (subterms t) ++ (Subterms rest) 
  end.

(** Useful characterization of [Subterms] *)
Lemma Subterms_char (T: list Term) (x: Term) :
  In x (Subterms T) <->
    exists t, In t T /\ In x (subterms t).
Proof.
  split.
  - intros H. 
    induction T as [ |t0 rest IH].
    + inv H.
    + simpl in H. apply in_app_or in H.
      destruct H as [H1 | H2].
      -- exists t0. auto.
      -- specialize (IH H2). 
         destruct IH as [t [H1 H3]].
         exists t; auto.

  -     induction T as [ |t0 rest IH].
        intros H.
        destruct H as [t [H1 H2]]; inv H1.

        intros H.
        destruct H as [t [H1 H2]].
        (* simpl in H1. *)
        destruct H1; subst; simpl; auto.

        apply in_or_app. right.  apply IH.
        now exists t.
Qed.

(* -------------------------------------------- *)
(**  [Subterms] is inflationary  *)
Lemma Subterms_incl (T: set Term) :
  T <<= Subterms T.
Proof.
  intros t H.
  apply Subterms_char. exists t.
  split. easy. apply in_subterms.
Qed.  
#[export] Hint Resolve Subterms_incl : core.

(** [Subterms] is monotone *)
Lemma Subterms_monotone (xs ys : list Term) :
 xs <<= ys ->
Subterms xs <<= Subterms ys.
Proof.
  intros Hss t Hin.
  rewrite Subterms_char in Hin.
  destruct Hin as [t0 [H1 H2]].
  assert (a: In t0 ys).
  { specialize (Hss t0 H1). easy. }
  apply Subterms_char.   now exists t0.
Qed.
#[export] Hint Resolve Subterms_monotone : core.

(* ----------------------------------- *)

(** ** Relate [Subterms] and [subterm_closed]  *)
Lemma subterm_closed_Subterms_if (u : set Term) :
  subterm_closed u -> Subterms u <<= u.
Proof.
  intros H x Hin.
  apply Subterms_char in Hin.
  destruct Hin as [t [H1 H2]].
  unfold subterm_closed in H. 
  specialize (H t H1). auto.
Qed.  
#[export] Hint Resolve subterm_closed_Subterms_if : core.


Lemma subterm_closed_Subterms_then (T : set Term) :
  Subterms T <<= T -> subterm_closed T .
Proof.
  unfold subterm_closed.
  intros H t H1. 
  intros x xInT.
  enough (In x (Subterms T)).
  - auto.
  - apply Subterms_char.
    now exists t.
Qed.
#[export] Hint Resolve subterm_closed_Subterms_then : core.

Lemma subterm_closed_Subterms_iff (T : set Term) :
  Subterms T <<= T <-> subterm_closed T .
Proof.
  split.  
  apply subterm_closed_Subterms_then.
  apply subterm_closed_Subterms_if.
Qed.
#[export] Hint Rewrite subterm_closed_Subterms_iff : core.

(* ----------------------------------- *)


(** Important property : [Subterms] of a set is [subterm_closed] *)
Lemma Subterms_subterm_closed (T: set Term) :
  subterm_closed (Subterms T).
Proof.
  unfold subterm_closed. intros x H.
  induction T as [ |t T' IH].
  - inv H.
  - 
    simpl in *.
    apply in_app_or in H. destruct H.
    + apply incl_appl.
      now apply subterms_subterm_closed.
    + apply incl_appr.
      auto.
Qed.
#[export] Hint Resolve Subterms_subterm_closed : core.


(** [Subterms] is a toplogical closure operator *)
(** Note that this is [equi] not [eq] *)
Corollary Subterms_closure (T: list Term) :
  Subterms (Subterms T) === Subterms T.
Proof.
  assert (a: Subterms T <<= Subterms (Subterms T)).
  { apply Subterms_incl. }
  assert (b: Subterms (Subterms T) <<= Subterms T).
  { apply subterm_closed_Subterms_if.
    apply Subterms_subterm_closed. }
  auto.
Qed.
#[export] Hint Resolve Subterms_closure : core.

Theorem subset_subterm_closed (w u : set Term):
  subterm_closed u ->
  w <<= u ->
  Subterms w <<= u.
Proof.
  intros H1 H2. 
  assert (a: Subterms w <<= Subterms u).
  { now apply  Subterms_monotone. }  
  assert (b: Subterms u <<=  u). 
  { now apply subterm_closed_Subterms_iff. }
  apply (incl_tran a b ). 
Qed.
#[export] Hint Resolve subset_subterm_closed : core.

(** ** Relate [Subterms]  and [subterms] *)

Lemma subterms_if_subtermP x t :
  subtermP x t -> 
  In x (subterms t) .
Proof.
  intros H.  induction H.
  - crush.
  - inv H; crush.
  - now apply subterms_trans with y.
Qed.    
#[export] Hint Resolve subterms_if_subtermP : core.

Lemma if_subterms_subtermP x t :
  In x (subterms t) ->
  subtermP x t .
Proof.
  intros H.
  induction t; crush.
  - apply in_app_or in H0; destruct H0.
    + crush.
      eapply subtermP_trans with t1.
      easy.
      apply subtermP_dir. apply imm_subtermP_pr1.
    + crush.
      eapply subtermP_trans with t2.
      easy.
      apply subtermP_dir. apply imm_subtermP_pr2.

  - apply in_app_or in H0; destruct H0.
    + crush.
      eapply subtermP_trans with t1.
      easy.
      apply subtermP_dir. apply imm_subtermP_en1.
    + crush.
      eapply subtermP_trans with t2.
      easy.
      apply subtermP_dir. apply imm_subtermP_en2.
  - crush.
    eapply subtermP_trans with t. 
    easy.
    apply subtermP_dir. apply imm_subtermP_hs.
Qed.
#[export] Hint Resolve if_subterms_subtermP : core.

Theorem subterms_subtermP x t :
  subtermP x t <-> 
  In x (subterms t) .
Proof.
  split.
  - intros H;  now apply subterms_if_subtermP.
  - intros H; now apply if_subterms_subtermP.
Qed.
#[export] Hint Rewrite subterms_subtermP : core.


(** If xs is a set of subterms of ys then the subterms of xs are all subterms of ys *)
Lemma subterms_subterms (xs ys : set Term) :
  xs <<= Subterms ys ->
  Subterms xs <<= Subterms ys.
Proof.
 intros H.
 apply Subterms_monotone in H.
 assert (a:= (Subterms_closure ys) ).
 eapply incl_tran with (Subterms (Subterms ys)).
 easy. now unfold equi in a.
Qed.
#[export] Hint Rewrite subterms_subterms : core.

(* ============================== *)
(** * General facts about [subterms] *)

Lemma subterm_refl (t: Term) :
  subtermP t t.
Proof.
apply subtermP_refl.
Qed.
#[export] Hint Resolve subterm_refl : core.
(* ============================== *)

(** * Domain-specific boilerplate about [subterms] *)

Lemma in_Subterms (ts: list Term) (t: Term) :
  In t ts ->
  In t (Subterms  ts).
Proof.
  intros H.
  apply Subterms_char.
  now exists t.
Qed.
#[export] Hint Resolve in_Subterms : core.

Lemma subterms_Subterms (ts: list Term) (t tsub: Term) :
  In t ts ->
  (subterms t) <<=  (Subterms  ts).
Proof.
  intros H1 t0 H2 .
  apply Subterms_char.
  now exists t.
Qed.
#[export] Hint Resolve subterms_Subterms : core.

(* --------------------------- *)

Lemma subterms_pr1 t1 t2 :
  In t1 (subterms (Pr t1 t2)).
Proof.
  simpl. right.
  apply in_or_app;  auto.
Qed.
#[export] Hint Resolve subterms_pr1 : core.

Lemma pr1_subterms (t t1 t2 : Term):
  In (Pr t1 t2) (subterms t) ->
  In t1 (subterms t).
Proof. 
  intros H. 
  apply (subterms_trans) with (Pr t1 t2);
  auto.
Qed.
#[export] Hint Resolve pr1_subterms : core.

Lemma pr1_Subterms (ts: list Term) (t1 t2 : Term) :
  In (Pr t1 t2) (Subterms ts) ->
  In t1 (Subterms ts).
Proof. 
  intros H.
  apply Subterms_char in H.
  apply Subterms_char.
  destruct H as [t [H1 H2]].
  apply pr1_subterms in H2.
  now exists t.
Qed.
#[export] Hint Resolve pr1_Subterms : core.

(* ---------------------------- *)

Lemma subterms_pr2 t1 t2 :
  In t2 (subterms (Pr t1 t2)).
Proof.
  simpl. right.
  apply in_or_app;  auto.
Qed.
#[export] Hint Resolve subterms_pr2 : core.

Lemma pr2_subterms (t t1 t2 : Term):
  In (Pr t1 t2) (subterms t) ->
  In t2 (subterms t).
Proof. 
  intros H. 
  apply (subterms_trans) with (Pr t1 t2);
  auto.
Qed.
#[export] Hint Resolve pr2_subterms : core.

Lemma pr2_Subterms  (ts: list Term) (t1 t2 : Term):
  In (Pr t1 t2) (Subterms ts) ->
  In t2 (Subterms ts).
Proof. 
  intros H.
  apply Subterms_char in H.
  apply Subterms_char.
  destruct H as [t [H1 H2]].
  apply pr2_subterms in H2.
  now exists t.
Qed.
#[export] Hint Resolve pr2_Subterms : core.

(* ---------------------------- *)
 
Lemma subterms_en1 t1 t2 :
  In t1 (subterms (En t1 t2)).
Proof.
  simpl. right.
  apply in_or_app;  auto.
Qed.
#[export] Hint Resolve subterms_en1 : core.

Lemma en1_subterms (t t1 t2 : Term):
  In (En t1 t2) (subterms t) ->
  In t1 (subterms t).
Proof. 
  intros H. 
  apply (subterms_trans) with (En t1 t2);
  auto.
Qed.
#[export] Hint Resolve en1_subterms : core.


Lemma en1_Subterms  (ts: list Term) (t1 t2 : Term):
  In (En t1 t2) (Subterms ts) ->
  In t1 (Subterms ts).
Proof. 
  intros H.
  apply Subterms_char in H.
  apply Subterms_char.
  destruct H as [t [H1 H2]].
  apply en1_subterms in H2.
  now exists t.
Qed.
#[export] Hint Resolve en1_Subterms : core.

(* --------------------------- *)

Lemma subterms_en2 t1 t2 :
  In t2 (subterms (En t1 t2)).
Proof.
  simpl. right.
  apply in_or_app;  auto.
Qed.
#[export] Hint Resolve subterms_en2 : core.

Lemma en2_subterms (t t1 t2 : Term):
  In (En t1 t2) (subterms t) ->
  In t2 (subterms t).
Proof. 
  intros H. 
  apply (subterms_trans) with (En t1 t2);
  auto.
Qed.
#[export] Hint Resolve en2_subterms : core.

Lemma en2_Subterms  (ts: list Term) (t1 t2 : Term):
  In (En t1 t2) (Subterms ts) ->
  In t2 (Subterms ts).
Proof. 
  intros H.
  apply Subterms_char in H.
  apply Subterms_char.
  destruct H as [t [H1 H2]].
  apply en2_subterms in H2.
  now exists t.
Qed.
#[export] Hint Resolve en2_Subterms : core.

(* --------------------------- *)

Lemma subterms_hs t1 :
  In t1 (subterms (Hs t1)).
Proof.
  simpl. right;  auto.
Qed.
#[export] Hint Resolve subterms_hs : core.

Lemma hs_subterms (t t1 : Term):
  In (Hs t1) (subterms t) ->
  In t1 (subterms t).
Proof. 
  intros H. 
  apply (subterms_trans) with (Hs t1 );
  auto.
Qed.
#[export] Hint Resolve hs_subterms : core.

Lemma hs_Subterms  (ts: list Term) (t1 t2 : Term) :
  In (Hs t1) (Subterms ts) ->
  In t1 (Subterms ts).
Proof. 
  intros H.
  apply Subterms_char in H.
  apply Subterms_char.
  destruct H as [t [H1 H2]].
  apply hs_subterms in H2.
  now exists t.
Qed.
#[export] Hint Resolve hs_Subterms : core.

(*
#[global]
Hint Resolve 
subt_list_in
 subt_list_pair1
 subt_list_pair2
 subt_list_en1
 subt_list_en2
 subt_list_hs
: core.
*)


