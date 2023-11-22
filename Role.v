(* Time-stamp: <Wed 11/22/23 11:24 Dan Dougherty Role.v> *)

From Coq Require Export List Bool Arith. 
Export ListNotations.

From RC Require Import
  CpdtTactics
  Utilities
  ListUtil
  Decidability
  Sorts
  Act
  Term
  Subterms
  (* Runtime *)
.


(** * Roles *)

(** A Role is a list of Actions (inputs, outputs, sends and receives)
    specified by Terms
*)

Definition Role :=  list (Act Term).

(** * Utilities *)

(** Extract the Terms in an action *)
Definition act_term_msg (e: Act Term): list Term :=
 match e with
     | Prm x => [x]
     | Ret x => [x]
     | Snd x1 x2 => [x1 ; x2]
     | Rcv x1 x2 => [x1 ; x2]
     end.

(** duplicates ok here *) 
Fixpoint act_term_msgs (rl: Role): Terms :=
  match rl with 
  | [] => []
  | a :: rest => act_term_msg a ++ act_term_msgs rest
 end.

(** Extract the Terms in a role *)
Definition terms_of_role (rl : Role): list Term :=
  nodup Term_eq_dec (act_term_msgs rl). 

(** This will be the "universe" of Terms during compilation *)

Definition Subterms_of_role (rl : Role): list Term :=
  Subterms (terms_of_role rl).



(* ================================== *) 

(** ** The Qt terms of a Role *)

(** need these for initialization *)

Definition quote_terms_in_role (rl: Role) : Terms :=
  filter is_quote (Subterms_of_role rl).

(* ---------------------------------------------- *)
(** ** Positive-polarity Terms *)

(** These are the elementary Terms that are constructed by the role.
    That is, if the first occurrence of an elementary term in in a
    send, it is counted here.

    We don't exclude outputs, although that would be anomalous in a
    protocol.

   Positive polarity is not the same as originating since subterms of
   keys are included in pos_pol.

    Implementation: a helper function accumulates all elementary terms
    seen so far paired with those that are first seen in a send or
    output.

    We don't bother about duplicates until later.  *)

Fixpoint pos_pol_helper (acc: Terms*Terms) (evts: list (Act Term)) 
  :=
  match evts with 
    [] => acc

  | Rcv c t :: rest => 
      pos_pol_helper 
        (Term.elems_of_terms [c;t] ++ fst acc, 
          snd acc)
        rest

  | Prm t :: rest => 
      pos_pol_helper 
        (Term.elems_of_terms [t] ++ fst acc, 
          snd acc)
        rest

  | Snd c t :: rest => 
      pos_pol_helper
        (* all elems get added to the fst *)
        (Term.elems_of_terms (fst acc) ++ [c;t] ,
          (* add to the snd if new  *)
          ListUtil.guarded_add (fst acc) (Term.elems_of_terms [t]) (snd acc))
        rest
        
  | Ret t :: rest => 
      pos_pol_helper
        (* all elems get added to the fst *)
        (Term.elems_of_terms (fst acc) ++ [t] ,
          (* add to the snd if new  *)
          ListUtil.guarded_add 
            (fst acc) 
            (Term.elems_of_terms [t])
            (snd acc))
        rest


  end.

(** Be careful to exclude inputs.
    We remove dups here *) 
Definition pos_pol_in_role (rl: Role) : Terms :=
  nodup Term_eq_dec 
    (snd (pos_pol_helper 
          ([], []) rl)).


