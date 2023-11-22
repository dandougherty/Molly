(* Time-stamp: <Wed 11/22/23 11:25 Dan Dougherty Reflecting.v> 
 *)

From Coq Require Import 
  String 
  List 
  Classical_Prop
  FunctionalExtensionality
  PropExtensionality
.
Import ListNotations.

From RC Require Import
  CpdtTactics
  TacticsMatch
  Utilities
  Decidability
  ListUtil
  Sorts
  Act
  Runtime
  Term
  Role
  TranscriptsRole
  Proc
  TranscriptsProc
  SaturationClass
  SaturationRules
  SaturationLoop
  Compile
  Reasoning
.

(** In this version we rely on the [Satd] typeclass *)

Section GoodPullback.

Context {RTV : RTVal}. (* determines [rtval] *)

(** Assume a saturated proc *)
Variable pr: Proc.
Context {S : @Satd pr}. 

(** Assume a good  store *)
Variable sto : loc -> rtval .
Hypothesis goodstore : good_store pr sto.


(** the Term-rtval composition of sto and cs.
    Recall that [tl] is the term-to-location relation 
    determined by the Proc
*)

Definition tv : rel Term rtval :=
  composeRF (tl pr) sto.

(* Our GOAL is to prove that [tv] is a 
[good_term_rtval] relation *)

(* ----------------------------------------------------- *)

(** a tactic to conveniently work with the goodness assumption *)

  Ltac des :=  destruct goodstore as
     [Sto_same 
       [Sto_sorts 
          [Sto_chash
             [Sto_inv 
                [Sto_pair
                   [Sto_encr
                      [Sto_hash
                         [Sto_quote 
                            [Sto_first 
                               [Sto_scnd 
                                  [Sto_decr
                                     [Sto_pubof
                                        Sto_cquote
          ]]]]]]]]]]]].
      

(* ----------------------------------- *)
 
(** * Functional *)

  Lemma tvFunctional :
    tv_functional tv .

  Proof. 
  intros t r1 r2 He H1 H2.
  inv H1. inv H.
  inv H2. inv H3.

  assert (h1:= @satd_sameness pr S t y y0 e e0 He H0 H4).
  eapply same_linked_same_value; eauto.
  apply goodstore.
Qed.
(* #[export] Hint Resolve tvFunctional : core. *)

(** * Sorts *)

(** Uses tv_functional *)
Lemma tvSorts: tv_sorts tv.

Proof. 
  intros t1 r Helem H1. 
  inv H1. inv H.
  des. 
  assert (h0:= @satd_sort_check pr S t1 y e Helem H0). 
  destruct h0 as [l' [e' [P1 P2]]].
  
  hnf in Sto_sorts.
  assert (h2:= @tvFunctional t1 (sto y) (sto l') Helem
                 ).

  specialize (Sto_sorts l' (sort_of t1) P2).
  rewrite <- Sto_sorts.
  f_equal.
  apply h2. 
  - constructor; easy.
  - constructor. econstructor; eauto.
Qed.

(** * Pairing *)

Lemma tvPair: tv_pair tv.
Proof. 
  intros t1 t2 r Htv. inv Htv. inv H.
 
  (* cases on whether e is a pair_expression_for the pair *)
  destruct (is_pair_expression_for pr (Pr t1 t2) e) eqn:e1. 
  { (* e is a pair_expression_for *)
    unfold is_pair_expression_for in *.
    destruct_all_matches.
    apply andb_true_iff in e1.
    destruct e1.
      apply (get_binding t1 l pr) in H1;
      destruct H1 as [e1 Q1].

      apply (get_binding t2 l0 pr) in H2;
      destruct H2 as [e2 Q2].


    exists (sto l) ; exists (sto l0) .
    split.
    constructor. econstructor; eauto.
    (* eapply tdecl_bound_intro; eauto. *)
    split. 
    constructor. econstructor; eauto.

    des.
    eapply Sto_pair; eauto.
  }
  { (* e is not a pair_expression_for *)
    assert (h1:= satd_pair_analyze H0 e1).

    destruct h1 as [h1l h1r].
    destruct h1l as [l1 P1].
    destruct h1r as [l2 P2].
    exists (sto l1) ; exists (sto l2) .
    split.
    constructor. econstructor; eauto.
    split. 
    constructor. econstructor; eauto.
 
    apply rtpairI. 
    des.
    specialize (Sto_first t1 y l1 P1).
    specialize (Sto_scnd t2 y l2 P2).
    tauto.
  }
Qed.

(** * Encryption *)
 
Lemma tvEncr: tv_encr tv.
Proof.  
  intros  t1 t2 r Htv. inv Htv.  inv H.
  (* cases on whether e _encr_expression_for the encryption *)
  destruct ((is_encr_expression_for pr (En t1 t2) e)) eqn:e1. 
  { (* e is an encr_expression_for *)
    left.
    unfold is_encr_expression_for in *.
    destruct_all_matches.
    apply andb_true_iff in e1.
    destruct e1.
      apply (get_binding t1 l pr) in H1;
      destruct H1 as [e1 Q1].

      apply (get_binding t2 l0 pr) in H2;
      destruct H2 as [e2 Q2].


    exists (sto l) ; exists (sto l0) .
    split.
    constructor.  econstructor; eauto.
    split. 
    constructor.  econstructor; eauto.

    des.
    eapply Sto_encr; eauto.
  }
  { (* e is not an  encr_expression_for *)
    right. 
    unfold decr_condition.

    assert (h1:= satd_decryption_keys).  
    hnf in h1.
    specialize (h1 t1 t2 y e H0 e1).
    destruct h1 as [kd [lkd [ekd [P1 P2]]]].

    assert (h2:= @satd_decryption _ _
           t1 t2 y e H0 e1 kd
           lkd ekd P1 P2).
    destruct h2 as [lp D].

    exists (sto lp) .
    exists (sto lkd) .

    des. 
    clear Sto_same Sto_sorts Sto_inv Sto_pair Sto_encr Sto_hash
      Sto_quote Sto_first Sto_scnd.
     unfold sto_decr in Sto_decr.

    split.
   { constructor.
     apply are_inv_then_inv in P2;  subst.  
     econstructor; eauto. 
   }
   split.
   {  constructor. econstructor; eauto. 
   }
    eapply Sto_decr; eauto.
  }
Qed.

(** * Hashing *)

Lemma tvHash :  tv_hash tv . 
  hnf.  
  intros t r Htv.
  inv Htv. inv H. 
  rename y into lh.
  rename e into eh.
 
  assert (h1:= @satd_hash_justified _ S t lh eh H0).
  destruct h1 as [lt [et Q]].
  exists (sto lt). split.
    - constructor. econstructor; eauto.
    - des.
      assert (h2:= @satd_hash_check _ S t lt lh et eh H0 Q).
      now apply Sto_chash. 
Qed.


(** * Quotation *)

Lemma tvQot : tv_qot tv.
Proof.  
  hnf. 
  intros s r H.
  inv H. rename y into lq.  
  inv H0.
 
  des;  clear Sto_same Sto_sorts Sto_inv
          Sto_pair Sto_encr Sto_hash Sto_first Sto_scnd
          Sto_decr Sto_chash Sto_pubof Sto_quote.
  hnf in Sto_cquote.
  symmetry.
  apply Sto_cquote.

  apply (@satd_qotChck pr S s
         lq e H1).
Qed.


Lemma tvKeyPair : tv_key_pair tv .
Proof.
  hnf.   
  intros t1 t2 r r0 H1 H2 H3 .
  inv H2. inv H. rename y into l1. rename e into e1.
  inv H3. inv H4. rename y into l2. rename e into e2.

  assert (h1:= @satd_key_pairs _ _ t1 t2 l1 l2 e1 e2
                             H1 H0 H5 ).

  des.
  hnf in Sto_inv.

  now apply Sto_inv.
  Qed.



Proposition good_satd_rl_pullback :
  good_term_rtval tv.
Proof.   
split. apply tvSorts .
split. apply tvFunctional.
split. apply tvPair .
split. apply tvHash.
split. apply tvKeyPair. 
split. apply tvEncr .
apply tvQot. 
Qed.

End GoodPullback.

(** ** Reflecting Transcripts Theorem *)

(** Need to show that

- tv pr sto is a good_term_rtval

- it makes the same role transcript as the given proc transcript

The first is the work in the section above

The second just uses the facts that (i) compilation makes traces line
up and (ii) composition is preserved by all the lifting through [Act]
and [List]

*)

Theorem reflecting_transcripts {RTV: RTVal} :
  forall 
    (rl: Role)
    (pr : Proc) (S: @Satd pr)
    (tr : list (Act rtval)),
    compileR rl pr ->
    transcript_for_procR pr tr ->
    transcript_for_role rl tr .
Proof.  
  intros rl pr S tr Hcompile Htr.
  destruct Htr as [sto [Hgood Htr] ].
  assert (pullback:= @good_satd_rl_pullback RTV _  _ sto 
         Hgood).

  unfold transcript_for_role.
  exists (tv pr sto).
  split. 
  - (* tv pr sto is a good_term_rtval *)
    easy.
  - (* we have the same raw transcript *) 
    assert (lineup := @compile_traces_tl rl pr Hcompile).
    hnf in lineup. 
    unfold tv in *.

    assert (a1 := composeRF_composeR (tl pr) sto).
    rewrite a1. clear a1.

    assert (a2:= compose_Act_mapRs ).
    rewrite -> a2.
    eapply List_mapR_compose; eauto.
Qed.

