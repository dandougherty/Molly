 (* Time-stamp: <Mon 4/15/24 11:50 Dan Dougherty Runtime.v>  *)

From Coq Require Import 
  String 
  List 
  Classical_Prop.
Import ListNotations.

From RC Require Import
  Utilities
  Decidability
  ListUtil
  Sorts
  Act
.

(** Important that rtfrst, rtscnd, and rdecr return option, since in a real
runtime these might fail.  This play a role in the "surjective
pairing" axiom pairI, which isn't surjective at all...  it says that
[ pair (rtfrst r) (rtscnd r)] is r IF those projections are
defined.

*)

 
Class RTVal := {
    rtval : Type ;
    rt_beq: rtval -> rtval -> bool;
    rt_beq_eq: forall x y, if rt_beq x y 
                           then x = y 
                           else x <> y;
    (* rtval_eq_dec :  *)
    (* forall x y : rtval, {x = y} + {~ x = y}; *)

    (** Operators *)
    rtsort : rtval -> sort ;

    rtpair : rtval -> rtval -> rtval  ;
    rtfrst : rtval -> option rtval ;
    rtscnd : rtval -> option rtval ;

    rtencr : rtval -> rtval -> rtval -> Prop ;
    rtdecr : rtval -> rtval -> option rtval ;

    rthash : rtval -> rtval  ;

    rtquote : string -> rtval ;
    genr : nat -> sort -> rtval  ;

    rtpubof : rtval -> option rtval;
    rtinv :  rtval -> rtval ;

    (** Axioms *)
    
    (** *** sorts *)

    rtgenr_sort :
    forall n srt, rtsort (genr n srt) = srt ; 
    
    (** *** pairing *)
    
    rtpairI
    : forall r r1 r2,
        (rtfrst r = Some r1 /\ rtscnd r = Some r2) ->
        rtpair r1 r2 = r ;

    (* pairEL and pairER  are not used!
      They would be needed for a version of Preserving Transcripts
     *)
    rtpairEL 
    : forall r1 r2, rtfrst (rtpair r1 r2) = Some r1;
    rtpairER
    : forall r1 r2, rtscnd (rtpair r1 r2) = Some r2; 

    (* ======================================== *)
    (** *** encryption and decryption *)

   rtDecrEncr 
     : forall (rp re rkd  : rtval) ,
           rtdecr re rkd = Some rp <->
           rtencr rp (rtinv rkd) re
       ;



  } .  (* end of Typeclass defn *)


(* ------------------- *)

Section RuntimeAux.

Context `{RTV : RTVal}. (* determines [rtval] *)


(** Converse of rtpairI is derivable *)

Lemma rtpairIE (r r1 r2: rtval) :
  rtpair r1 r2 = r  -> 
  (rtfrst r = Some r1 /\ rtscnd r = Some r2).
Proof.
 intros h.
 split. 
 + rewrite <- h.
   apply rtpairEL.

 + rewrite <- h.
   apply rtpairER.
Qed.


(** *** Notion of runtime key pair is definable *)
Definition rtkypr (r1 r2 : rtval) : Prop :=
  rtpubof r1 = Some r2.

End RuntimeAux.

(* ------------------- *)

Notation transcript := (list (Act rtval)).


