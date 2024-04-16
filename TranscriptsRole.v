(* Time-stamp: <Mon 4/15/24 11:12 Dan Dougherty TranscriptsRole.v> *)

(**  
   
    There is a real duality between encrytion and decryption,
    expressed in [Runtime.rtencr_iff].
    Namely, that when rkd and rke are runtime inverses,

    [rtencr rp rke re] if and only if [decr re rkd = Some rp]

    When working with neutral expressions, ie when the expression is
    not explicitly an [_Encr], it is natural to use decryption rather
    than encryption.  We might hope for an equivalence at the symbolic
    level.  But we can't because at the symbolic level not every term
    [t] has an inverse.  More precisely we can't always identify a
    symbolic term [t'] which is guranteed to be evauated to the
    runtime inverse of [t], even by well-behaved term-valuations.
    This is an essential feature of non-deterministic encryption.

    There is awkwardness even in formulating an equivalence at the
    runtime level, dues to the fact that a given [tv] might not be
    defined for both parts of a symbolic key pair (in particular, for
    the case we care about, when the [tv] is defined by pulling back
    along the statements of an eproc.

    Ultimately this is only a programming inconvenience since gven a
    tv it is natural to "complete" it by extending its domain to
    include both parts of a key pair whenever a key is in the domain.
    But we don't bother to do this (for now).  As a consequence we
    simply build the two approaches (the inro and the elim) into the
    DEFN of good term valuation.
*)

From Coq Require Export List Bool Arith. (* Includes PeanoNat *)
Export ListNotations.
 
From RC Require Import
  CpdtTactics
  Utilities
  ListUtil
  Decidability
  Sorts
  Act
  Runtime
  Term
  Subterms
  Role

.

(** * Runtime semantics of roles  *)

(**
The starting point is a RELATION from terms to runtime values.

This is in contrast to the definition of transcript for a proc (or an
eproc), where we start with a FUNCTON from locations to runtime values
(respectively, from eterms to runtime values).   This is unavoidable 
since different term occurrences can have different values.

*)
Section TermVal.

  Context {RTV : RTVal}.

  (** The properties we will insist on for a termVal *)
  Section termValProps.

    (* Variable rl: Role. *)
    Variable tv: rel Term rtval.

    (** respect sorts *)
    Definition tv_sorts :=      forall t r, 
        is_elementary t ->
        tv t r ->
        rtsort r = sort_of t.

    (** non-determinism can only arise from non-determinstic
    constructors ... tv is a function on elelmentary terms *)

    Definition tv_functional :=
      forall t r1 r2,
        is_elementary t ->
        tv t r1 -> tv t r2 -> 
        r1 = r2.

    (** pairing: the obvious condition *)

    Definition tv_pair := 
      forall t1 t2 r,
        tv (Pr t1 t2) r ->
        exists r1 r2, 
          (tv t1 r1 /\ tv t2 r2 /\
             rtpair r1 r2 = r).

    (** hashing: the obvious condition *)

    Definition tv_hash := 
      forall t1 r,
        tv (Hs t1) r ->
        exists r1, 
          tv t1 r1 /\
            rthash r1 = r .

    (** quotation: the obvious condition *)

    Definition tv_qot :=
      forall  s (r: rtval),
        tv (Qt s) r ->
        r = rtquote s.


    (* -------------------------------------- *)
    (** inverses : subtle! *)
    
    Definition tv_key_pair :=
      forall t t' (r r' : rtval),
        makes_key_pair t t' = true ->
        tv t r ->
        tv t' r' ->
        rtkypr r r'.
    (* rtkypr r r' = true. *)
 
    (** says that tv maps both parts of a key pair
        
        we do NOT use this one *)

    Definition tv_key_pair_strong:=
      forall t t' r ,
        makes_key_pair t t' = true ->
        tv t r ->
        exists r',
          tv t' r' .

    (* -------------------------------------- *)
    (** encryption *)

    (** encryption needs care.
        See discussion at the top of this file.  *)

    (* the obvious condition for when the encryption is being
    constructed *)

    Definition encr_condition 
      (p ke : Term) (re : rtval)  :=
      exists (rp rke : rtval),
        tv ke rke 
        /\ tv p rp  
        /\ rtencr rp rke re.


    (** note that here we do not say anything about having the
        encryption key, rather that we have access to the decryption
        key *)

    Definition decr_condition 
      (p ke : Term) (re : rtval) :=
      exists (rp rkd: rtval),
        tv (inv ke) rkd
        /\ tv p rp 
        /\ rtdecr re rkd = Some rp .

    Definition tv_encr : Prop :=
      forall (p ke : Term) (re : rtval), 
        tv (En p ke) re ->
        (encr_condition p ke re 
         \/ decr_condition p ke re) .



   End termValProps.


  (** *** Main definition for termVals  *)

  Definition good_term_rtval (tv: rel Term rtval) := 
    tv_sorts tv  
    /\ tv_functional tv
    /\ tv_pair tv 
    /\ tv_hash tv
    /\ tv_key_pair tv
    /\ tv_encr tv 
    /\ tv_qot tv
  .



End TermVal.

(** * Transcripts for roles, from termVals
 *)

(** the role is needed to express that the acions line up
*)
Definition transcript_for_role `{RTVal}
  (rl: Role) (tr : transcript) : Prop 
  :=  exists (tv: rel Term rtval), 
    good_term_rtval tv
    /\ List_mapR (Act_mapR tv) rl tr. 
