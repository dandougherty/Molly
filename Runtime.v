 (* Time-stamp: <Wed 11/22/23 11:27 Dan Dougherty Runtime.v>
 *)

(** We only state as axioms the facts about pairing and unpairing,
because those are the ony axioms we need for Reflecting Transcripts.

We don't even need the encryption-decryption duality, because we use
the disjunctive condition in the defn of role transcripts.

This is all a refelction of the relatively unambitious correctness
condition we prove.

*)

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
    rtval_eq_dec : 
    forall x y : rtval, {x = y} + {~ x = y};

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

    rtkypr : rtval -> rtval ->  bool;

    (** Axioms *)
    
    (** *** sorts *)

    rtgenr_sort :
    forall n srt, rtsort (genr n srt) = srt ; 
    
    (** *** pairing *)
    
    rtpairEL 
    : forall r1 r2, rtfrst (rtpair r1 r2) = Some r1;
    rtpairER
    : forall r1 r2, rtscnd (rtpair r1 r2) = Some r2; 
    rtpairI
    : forall r r1 r2,
      rtpair r1 r2 = r  <->
        (rtfrst r = Some r1 /\ rtscnd r = Some r2);
    

    (** *** [rtkypr] vs [rtpubof] *)

    pubof_keypair
      : forall r1 r2, rtkypr r1 r2 = true <->
                        (rtpubof r1 = (Some r2))  ;



  } .  (* end of Typeclass defn *)


(* ------------------- *)

Notation transcript := (list (Act rtval)).


