  (* Time-stamp: <Wed 11/22/23 11:34 Dan Dougherty TranscriptsProc.v> *)

From Coq Require Import
 String List
Relations.
Import ListNotations.

From RC Require Import
  Utilities
  ListUtil
  Decidability
  Act
  Sorts
  Term
  Role
  (* Eproc *)
  Proc
  Runtime
  (* Compile *)
.
Unset Implicit Arguments.

(* ============================================ *)
(** * Transcripts for a Proc *)

Section ProcVal.
  
  Context {RTV : RTVal}.
  Variable pr: Proc. 
  Variable sto: loc -> rtval.
  

  (** ** Coherence conditions that we'll impose on a sequence of
  rtvals in order to support a transcript *)


  (** *** compositionality requirements *)

(* ----------------------------------------------- *)

  Definition sto_pair := 
    forall (t: Term) (l l1 l2 :loc) ,
      In (Bind (t , l) (Pair l1 l2)) pr -> 
      rtpair (sto l1) (sto l2) = (sto l) .

  Definition sto_frst := 
    forall (t: Term) (l l1: loc) ,
      In (Bind (t , l1) (Frst l)) pr ->
      (rtfrst (sto l)) = Some (sto l1) .

  Definition sto_scnd := 
    forall (t: Term) (l l1: loc) ,
      In (Bind (t , l1) (Scnd l)) pr ->

      (rtscnd (sto l)) = Some (sto l1) .

  Definition sto_pubof := 
    forall (t: Term) (l l1: loc) ,
      In (Bind (t , l1) (PubOf l)) pr ->

      (rtpubof (sto l)) = Some (sto l1) .

(* ----------------------------------------------- *)

  Definition sto_encr := 
    forall (t: Term) (l l1 l2 :loc),
      In (Bind (t , l) (Encr l1 l2)) pr ->
      rtencr (sto l1) (sto l2) (sto l).

  (* [lp] is location of plaintext
     [le] is location of encryption
     [lkd] is location of decryption key  *)

  Definition sto_decr := 
    forall (t: Term) (lp le lkd: loc) ,
      In (Bind (t , lp) (Decr le lkd)) pr ->
      rtdecr (sto le) (sto lkd) = Some (sto lp) .



(* ----------------------------------------------- *)

(** @@ This has different character from sto_pair, sto_encr: it says
    that the sto-value of the location must correlate with the TERM,
    not the associated EXPR *)

  Definition sto_quoteOLD := 
    forall (l: loc)(e : Expr) (s: string) , 
      In (Bind ((Qt s) , l) e) pr ->
      (sto l) = (rtquote s) .

  Definition sto_quote := 
    forall (t: Term)  (l: loc) (s: string) , 
      In (Bind (t , l ) (Quote s)) pr ->
      (sto l) = (rtquote s) .

(* ----------------------------------------------- *)

  Definition sto_hash := 
    forall (t: Term)(l l1 :loc),
      In (Bind (t , l) (Hash l1)) pr ->
      (sto l) = rthash (sto l1) .

  (** *** obeying the tests *)

  Definition sto_same : Prop :=
    forall l1 l2,
      In (Csame l1 l2) pr ->
      sto l1 = sto l2.
      
  Definition sto_sorts : Prop :=
    forall l s,  
      In (Csrt l s ) pr ->
      rtsort (sto l) = s.

  Definition sto_chash : Prop :=
    forall lh lt ,  
      In (Chash lh lt ) pr ->
      rthash (sto lt) = sto lh.

  Definition sto_cquote : Prop :=
    forall l s ,  
      In (Cquote l s) pr ->
      rtquote(s) = sto l.

  Definition sto_inverse : Prop :=
    forall  l1 l2 ,
      In (Ckypr l1 l2) pr ->
      rtkypr (sto l1) (sto l2) = true.


End ProcVal. 


Definition good_store
  `{_: RTVal} (pr: Proc) (sto: loc -> rtval) :=

  sto_same pr sto
  /\ sto_sorts pr sto
  /\ sto_chash pr sto
  /\ sto_inverse pr sto
  /\ sto_pair  pr sto
  /\ sto_encr pr sto
  /\ sto_hash pr sto 
  /\ sto_quote pr sto
  /\ sto_frst pr sto
  /\ sto_scnd pr sto
  /\ sto_decr pr sto
  /\ sto_pubof pr sto
  /\ sto_cquote pr sto
.

(** Convenient later *)


Lemma same_linked_same_value 
 `{_: RTVal} (pr: Proc) (sto: loc -> rtval) (l1 l2 : loc)  :
  same_linked pr l1 l2 ->
  sto_same pr sto ->
  sto l1 = sto l2.

Proof.
intros Hl Hs.
induction Hl.
- apply (Hs x y); auto.
- easy.
- symmetry; easy.
- congruence.
Qed.

(** * Transcripts for procs *)
Definition transcript_for_proc `{RTVal}
  (pr: Proc) (tr: transcript) : Prop :=
  exists (sto:  loc -> rtval), 
    good_store pr sto  
    /\ tr = map (Act_map sto) (prtrace pr).


Definition transcript_for_procR  `{RTVal}
  (pr: Proc) (tr: transcript) : Prop :=
  exists (sto:  loc -> rtval), 
    good_store pr sto  
    /\ List_mapR (Act_mapR (rel_of sto)) (prtrace pr) tr.

(* ============================================ *)






