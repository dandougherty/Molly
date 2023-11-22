   (* Time-stamp: <Wed 11/22/23 11:27 Dan Dougherty SaturationClass.v>
 *)


From Coq Require Import 
  List 
  String 
  Classical_Prop
  Classical_Pred_Type
  Wellfounded
  Relations
.
Import ListNotations.

From RC Require Import
  CpdtTactics
  Utilities
  Decidability
  ListUtil
  (* Iteration *)
  Act
  Sorts
  (* Runtime *)
  Term
  Role
  Proc
.

(** * A typeclass for saturation  *)

(* ------------------------------ *)
(** *** the eliminations *)

Definition ax_pair_analyze (pr: Proc) :=
  forall (t1 t2: Term) (l: loc) (e: Expr),
    In (Bind ((Pr t1 t2), l) e) pr ->
    (is_pair_expression_for pr (Pr t1 t2) e) = false ->
    (* ~ (is_pair_exp e) -> *)
    (exists (l1 : loc), In (Bind (t1 , l1) (Frst l)) pr) 
    /\ (exists (l2: loc), In (Bind (t2 , l2) (Scnd l)) pr).


Definition ax_decryption  (pr: Proc) := 
  forall (p k: Term) (le : loc) (ee: Expr),
    In (Bind ((En p k), le)  ee) pr ->
    (* ~ (is_encr_exp ee) -> *)
    (is_encr_expression_for pr
           (En p k) ee) = false ->
forall (kd: Term) (lkd : loc) (ekd: Expr),
      In (Bind (kd, lkd) ekd) pr  ->
      are_inv k kd ->
      exists (lp: loc),
        In (Bind (p, lp) (Decr le lkd)) pr  .

(* ------------------------------ *)
(* *** the checks *)

Definition ax_hash_check (pr: Proc) :=
  forall t lt lh et eh,
    In (Bind ((Hs t), lh) eh) pr  ->
    In (Bind (    t , lt) et) pr  ->
    In (Chash lh lt) pr  .


Definition ax_qotChck (pr: Proc) :=
  forall (s: string) l e  ,
    In (Bind ((Qt s), l)  e) pr ->
    (In (Cquote l s) pr) . 


Definition ax_key_pairs (pr: Proc) :=
  forall (t1 t2: Term) l1 l2 e1 e2 ,
    makes_key_pair t1 t2 = true ->
    In (Bind (t1, l1)  e1) pr ->
    In (Bind (t2, l2)  e2) pr ->
    (In (Ckypr l1 l2) pr) 
.

 Definition ax_sort_check (pr: Proc) :=
  forall (t : Term)(l: loc) (e : Expr),
    is_elementary t ->
    In (Bind (t,l) e) pr ->
    exists l' e', 
      In (Bind (t,l') e') pr /\
        In (Csrt l' (sort_of t)) pr  .


Definition ax_sameness (pr: Proc) : Prop :=
 forall (t: Term) (l1 l2 : loc) (e1 e2: Expr),
   (is_elementary t) ->
   In (Bind (t, l1) e1) pr ->
   In (Bind (t, l2) e2) pr ->
   same_linked pr l1 l2.


(*----------------------------------------*)
(** *** the justification conditions *)

Definition ax_hash_justified (pr: Proc) :=
  forall t  lh  eh,
    In (Bind ((Hs t), lh) eh) pr  ->
    exists lt et,
      In (Bind (  t , lt) et) pr  .


(** this says that decryption keys are available *)
(** if this fails it's the Role's fault *)

Definition ax_decryption_keys  (pr: Proc) := 
  forall (p k: Term) (le : loc) (ee: Expr),
    In (Bind ((En p k), le)  ee) pr ->
    (* ~ (is_encr_exp ee) -> *)
      (is_encr_expression_for pr
             (En p k) ee) =false ->
        exists (kd: Term) (lkd : loc) (ekd: Expr),
          In (Bind (kd, lkd) ekd) pr 
      /\ are_inv k kd  .


(*----------------------------------------*)

(** ** the axioms *)

(** The axioms here do NOT reflect the I-rules.  Those are not used in
Reflecting Transcripts, specifically we don't use then in arguiung
that we pull back to a good term_val.

The I-rules get used in order to be sure that saturation is rich enough
to derive all the bindings we should derive (Dolev-Yao speaking) *) 

Class Satd {cpr: Proc} := {

    satd_pair_analyze : ax_pair_analyze cpr ;
    satd_decryption : ax_decryption cpr ;

    satd_sameness: ax_sameness cpr ;
    satd_hash_check : ax_hash_check cpr ;
    satd_sort_check : ax_sort_check cpr ;
    satd_key_pairs : ax_key_pairs cpr ;
    satd_qotChck : ax_qotChck cpr ;

    satd_hash_justified : ax_hash_justified cpr ;
    satd_decryption_keys : ax_decryption_keys cpr ;

  } .





