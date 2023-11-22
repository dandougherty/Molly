(* Time-stamp: <Wed 11/22/23 11:28 Dan Dougherty SaturationLoop.v> *)
 From Coq Require Import 
  List 
  String 
  Classical_Prop
  Classical_Pred_Type
  Wellfounded
.
Import ListNotations.

From RC Require Import
  CpdtTactics
  TacticsMatch
  Utilities
  Decidability
  ListUtil
  Iteration
  Act
  Sorts
  Term
  Role
  Proc
  SaturationClass
  SaturationRules
.


(** ** The Closure loop *)
(* ======================================= *)
Section Close.

  Variable unv: Terms.

  (** Firing the closure rules to acheive being closed *)

  Definition max_term_size : nat :=
    list_max (map size_term unv).

  Definition do_step (pr: Proc) : Stmts :=
    apply_first_not_nil
      [
        do_pairE ;
        do_encrE ;
        do_hashChck ;

        do_pairI unv ;
        do_encrI unv;
        do_hashI unv ;

        do_qotChck ;
        do_sortChck ;
        do_sameChck ;
        do_kyprChck
      ] pr.

  Lemma do_step_is (pr: Proc) :
      do_step pr = do_pairE pr
    \/   do_step pr = do_encrE pr
    \/   do_step pr = do_hashChck pr

    \/   do_step pr = do_pairI unv pr
    \/   do_step pr = do_encrI unv pr
    \/   do_step pr = do_hashI unv pr

    \/   do_step pr = do_qotChck pr
    \/   do_step pr = do_sortChck pr
    \/   do_step pr = do_sameChck pr
    \/   do_step pr = do_kyprChck pr .
  Proof.
    unfold do_step;
      unfold apply_first_not_nil;
      (* destruct (do_pairEL pr); *)
      destruct (do_pairE pr);
      destruct (do_encrE pr);
      destruct (do_hashChck pr);

      destruct (do_pairI unv pr);
      destruct (do_encrI unv pr);
      destruct (do_hashI unv pr);

      destruct (do_qotChck pr);
      destruct (do_sortChck pr);
      destruct (do_sameChck pr);
      destruct (do_kyprChck pr);
      tauto. 
  Qed. 

Definition close_step (pr: Proc) : Proc :=
  pr ++ (do_step pr).

Lemma close_step_is (pr: Proc) :
  close_step pr = pr ++ do_pairE pr
  (* \/   close_step pr = pr ++ do_pairER pr *)
  \/   close_step pr = pr ++ do_encrE pr
  \/   close_step pr = pr ++ do_hashChck pr

  \/   close_step pr = pr ++ do_pairI unv  pr
  \/   close_step pr = pr ++ do_encrI unv pr
  \/   close_step pr = pr ++ do_hashI unv pr

  \/   close_step pr = pr ++ do_qotChck pr
  \/   close_step pr = pr ++ do_sortChck pr
  \/   close_step pr = pr ++ do_sameChck pr
  \/   close_step pr = pr ++ do_kyprChck pr.

Proof.
  unfold close_step.
  assert (h:= do_step_is pr).
  destruct h as 
    [h1 | [h2 | [h3 | [h4 | [h5 | [h6 | [h7 | [h8 | [h9 |  h10]]]]]]]]].

  rewrite h1; tauto.
  rewrite h2; tauto.
  rewrite h3; tauto.
  rewrite h4; tauto.
  rewrite h5; tauto.
  rewrite h6; tauto.
  rewrite h7; tauto.
  rewrite h8; tauto.
  rewrite h9; tauto.
  rewrite h10; tauto.
Qed.

Definition close_steps_n  : nat -> Proc -> Proc :=
   loop (close_step).

Definition proc_measure (pr: Proc) : nat :=
    ((length unv) + (3 * max_term_size)) .

Definition close (pr: Proc) : Proc :=
  close_steps_n (proc_measure pr) pr .

(* -----------------------*)
(** For testing *)
Definition close_n_diff 
  (n: nat) (pr: Proc) : Proc:=
  set_diff (close_steps_n n pr) 
  pr.

Definition close_diff 
  (pr: Proc) : Proc:=
  set_diff (close pr) pr.

End Close.


(* ------------------------------ *)
(** * Properties *)
 
(** ** Closed *)

Definition closed
  (unv : Terms) (pr: Proc) := 
   pairE_closed pr
  /\ pairI_closed unv pr

  /\ encrE_closed pr
  /\ encrI_closed unv pr

  /\ hashI_closed unv pr
  /\ hashChck_closed pr

  /\ sameChck_closed pr
  /\ sortChck_closed pr
  /\ qotChck_closed pr
  /\ kyprChck_closed pr
.
#[export] 
Instance closed_dec :
  forall (unv: Terms) (pr: Proc) ,
    (Decision (closed unv pr)).
Proof.
  intros unv pr.  unfold closed.
  apply _.
Defined.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** ** Justified *)

(** Do we have all the minor premisses we should ? *)

(**  *** Justified Hashes *)
(* *)
(** A hash is justified if we know its body *)

Definition hash_justified 
  (pr: Proc) (s: Stmt)  :=
  match s with 
   | (Bind ((Hs t), _) _) =>
       term_is_bound pr t

  | _ => True
  end.

#[export]
  Instance hash_justified_dec :
  forall pr s, Decision (hash_justified pr s).
Proof.
  intros pr s.
  unfold hash_justified;
    destruct s; auto.
  destruct t; auto.
  destruct t; auto.  
  apply term_is_bound_dec.
Defined.

(** IF smt is a bind of some [Hs t] then [t] is bound as well *)

Definition hash_justifiedb (pr: Proc) (smt: Stmt) :bool :=
  match smt with
    Bind ((Hs t), _ ) _ =>
      term_is_boundb pr t
                     
  |_ => true
  end.

Definition hashes_justified (pr: Proc) : Prop :=
  forall s, In s pr -> hash_justified pr s.
(* *)
Global Instance hashes_justified_dec pr :
  Decision (hashes_justified pr).
apply _.
Defined.
 


Definition hashes_justifiedb (pr: Proc) : bool :=
  forallb (hash_justifiedb pr) pr.



(**  *** Justified Encryptions *)

(** An encryption is [justified] if either we built it or the symbolic
inverse of its encryption key is available *)

Definition encryption_justifiedb
  (pr: Proc) (smt: Stmt) : bool :=
  match smt with
   (Bind ((En p k), _) ee) =>
     is_encr_expb ee || 
       term_is_boundb pr (inv k)

  | _ => true
end.

Definition encryptions_justifiedb (pr: Proc) :=
  forallb (encryption_justifiedb pr) pr.

Definition encryption_justified
  (pr: Proc) (smt: Stmt) : Prop :=
  match smt with
   (Bind ((En p k), _) ee) =>
     (* is_encr_exp ee \/  *)
        (is_encr_expression_for pr
             (En p k) ee) = true \/
          term_is_bound pr (inv k)

  | _ => True
end.
Global Instance encryption_justified_dec pr smt :
  Decision (encryption_justified pr smt).
Proof.
  hnf. 
  (* unfold hash_justified. *)
  destruct smt as [[ t l] e | ev | l1 l2 | l1 l2 | l1 l2 |  l s | l s |s].
  shelve.
  all: left; simpl;  easy.
  Unshelve. 
  destruct t.
  10: shelve.
  all: left; simpl;  easy.  
  Unshelve.
  unfold encryption_justified.
  apply or_dec;  apply _.
Defined.

Definition encryptions_justified (pr: Proc) : Prop :=
  forall s, In s pr ->  encryption_justified pr s.
Global Instance encryptions_justified_dec pr :
  Decision (encryptions_justified pr ).
Proof.
apply _.
Defined.

(** *** Justified *)

Definition justified_pr (pr: Proc) :=
  hashes_justified pr
  /\ encryptions_justified pr .
(* *)
#[export]
Instance justified_pr_dec :
  forall pr, Decision (justified_pr pr).
Proof.
apply _.
Defined.


Definition justifiedb_pr (pr: Proc) : bool :=
  hashes_justifiedb pr && encryptions_justifiedb pr .



(** ** Summary : Saturation *)


Definition saturated_pr 
  (unv: Terms) (pr: Proc) : Prop  :=
  closed unv pr  
  /\ justified_pr pr
.

(* *)
#[export] Instance saturated_pr_dec :
  forall (unv: Terms) (pr: Proc) ,
    (Decision (saturated_pr unv pr)).
Proof.
  intros unv pr.  apply _.
Defined.


(** To saturate is to do closure, then 
    test for being justified  
*)


Definition saturate
  (unv: Terms) (pr: Proc) : optionE Proc :=
  let closepr := (close unv pr) in 

  match decide (closed unv closepr) with
    right _ => NoneE
                 "saturation leaves non-closed proc"
  | left _ =>
      match decide (justified_pr closepr) with
      | right _ => NoneE
                     "saturation leaves unjustified proc"
      | left _ => 
          SomeE closepr
          end end 
 .


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(** * Proofs *)

     
(** ** Proofs about the empty pr *)
(* --- *)

(** The initial, empty, pr will be saturated *)
Lemma empty_saturated_pr :
  forall unv, saturated_pr unv [].
Proof.
  unfold saturated_pr.
  intros; split.
  -  unfold closed.
     split;
     hnf; intros; easy.
  - split;    hnf; intros; easy.
Qed.

(** ** Proofs about Closedness *)

(** ***  Closing Yields Closed *)
(**
This asserts that we have reached a fixed point for the saturation rules.
If this fails it is a program bug, eg not doing enough iterations.

Not used currently
*) 


(* Theorem close_is_closed : *)
(*   forall (unv: Terms) (pr: Proc), *)
(*           closed unv (close unv pr) . *)


(** *** Succesful saturation is really closing *)

Lemma sat_is_close unv pr pr' :
  saturate unv pr = SomeE pr' ->
  pr' = close unv pr.
Proof.
  intros H.
  unfold saturate in H.
  destruct_all_matches.
Qed.

Lemma saturate_gives_saturated unv pr pr' :
  saturate unv pr = SomeE pr' ->
  saturated_pr unv pr'.
Proof.
  unfold saturate;   unfold saturated_pr; intros H.
  destruct_all_matches. crush.
Qed.


(** ** Proofs about Justified *)

Lemma hashes_justified_then pr t lh eh  :
  hashes_justified pr ->
  In (Bind ((Hs t), lh) eh) pr ->
  exists lt et, 
    In (Bind (t,lt)  et) pr.
Proof. intros H1 H2.
       unfold hashes_justified in *.
       specialize (H1 (Bind ((Hs t),lh) eh) H2). 
       unfold hash_justified in *.
       apply H1.
Qed.


Lemma encryptions_justified_then pr p k le ee  :
  encryptions_justified pr ->
  In (Bind ((En p k), le) ee) pr -> 
  (* is_encr_exp ee \/ *)
  (is_encr_expression_for pr
             (En p k) ee) = true \/
    exists ld ed, 
    In (Bind ( (inv k) , ld)  ed) pr.
Proof. intros H1 H2.
       unfold encryptions_justified in *.
       specialize (H1 (Bind ((En p k), le) ee) H2) .
       unfold encryption_justified in *.
       destruct H1.
       - now left.
       - right.
         hnf in H.
         apply H.
Qed.

(**  ** Saturation is inflationary *)

(* prove it for one close-step *)
 
Lemma close_step_superset sts unv :
  subset sts (close_step unv sts).
Proof.
  assert (h:= close_step_is unv sts). 
  assert (h0:= subset_app_introR).
  apply h0.
Qed.

(* thence for any number of steps *)

Proposition close_steps_superset sts unv k :
  subset sts (close_steps_n unv k sts). 
Proof.
  unfold close_steps_n.
  apply Iteration.pre_post.
  - unfold reflexive. 
    apply subset_refl.
  - unfold transitive.
    apply subset_trans.
  - intros. apply close_step_superset.
Qed.

Theorem saturate_superset (unv: Terms) (sts x: list Stmt) :
  saturate unv sts = SomeE x ->
  subset sts x.
Proof. 
  intros H.
  unfold saturate in H.
  destruct_all_matches.
  inv H.
  apply close_steps_superset.
Qed.

(** ** Saturation doesn't change the trace *)

(* boilerplate, each rule, ... zzzzz *)

Lemma do_pairE_trace sts :
  prtrace (do_pairE sts) = [].   
Proof. 
  unfold do_pairE;
  destruct (pick_pairE_redex sts). 
  unfold fire_pairE.
  destruct x.
  (* destruct (proj1_sig s). *)
  destruct t; destruct t. 
 all: auto.
Qed.


Lemma do_encrE_trace sts :
  prtrace (do_encrE sts) = [].   
Proof.
  unfold do_encrE;
  destruct (pick_encrE_redex sts);
  unfold fire_encrE.
  destruct (proj1_sig s).
  destruct s0. destruct t. 
  all: auto.
  destruct t.
  all: auto.
  destruct s1.
  all: auto.
  destruct t.
  all: auto.
Qed.

Lemma do_hashChck_trace sts :
  prtrace (do_hashChck sts) = [].   
Proof.
  unfold do_hashChck;
  destruct (pick_hashChck_redex sts);
  unfold fire_hashChck.
  destruct (proj1_sig s).
  destruct s0. all: auto.
  destruct t. all: auto.
  destruct t. all: auto.
  destruct s1. all: auto.
  destruct t0 as [t3 ln].
  destruct (decide (t=t3)). all: auto.
Qed.


Lemma do_pairI_trace unv sts :
  prtrace (do_pairI unv sts) = [].   
Proof.
  unfold do_pairI;
  destruct (pick_pairI_redex unv sts);
  unfold fire_pairI.
  destruct x; auto.
  destruct s; auto.
  destruct t; auto.
  destruct s0; auto.
  destruct t0; auto.
  auto.
Qed.

Lemma do_encrI_trace unv sts :
  prtrace (do_encrI unv sts) = [].   
Proof.
  unfold do_encrI;
  destruct (pick_encrI_redex unv sts);
  unfold fire_encrI.
  destruct x; auto.
  destruct s; auto.
  destruct t; auto.
  destruct s0; auto.
  destruct t0; auto.
  auto.
Qed.

Lemma do_hashI_trace unv sts :
  prtrace (do_hashI unv sts) = [].   
Proof.
  unfold do_hashI;
  destruct (pick_hashI_redex unv sts);
  unfold fire_hashI.
  destruct x; auto.
  destruct t; auto.
  auto.
Qed.

Lemma do_qotChck_trace sts :
  prtrace (do_qotChck sts) = [].   
Proof.
  unfold do_qotChck;
  destruct (pick_qotChck_redex sts);
  unfold fire_qotChck.
  destruct (proj1_sig s).
  destruct t; destruct t. 
 all: auto.
Qed.

Lemma do_sortChck_trace sts :
  prtrace (do_sortChck sts) = [].   
Proof.
  unfold do_sortChck;
  destruct (pick_sortChck_redex sts);
  unfold fire_sortChck.
  destruct (proj1_sig s).
  destruct t; destruct t. 
 all: auto.
Qed.

Lemma do_sameChck_trace sts :
  prtrace (do_sameChck sts) = [].   
Proof.
  unfold do_sameChck;
  destruct (pick_sameChck_redex sts);
  unfold fire_sameChck.
  destruct (proj1_sig s); auto.
  - destruct t; auto.
  - auto.
Qed.

Lemma do_kyprChck_trace sts :
  prtrace (do_kyprChck sts) = [].   
Proof.
  unfold do_kyprChck;
  destruct (pick_kyprChck_redex sts);
  unfold fire_kyprChck.
  destruct (proj1_sig s).
  destruct s0; auto.
  destruct t; auto.
  destruct s1; auto. 
 all: auto.
 destruct t0; auto.
Qed.


(* prove it for one close_step, using all the individual step results
*)
Lemma close_step_trace sts unv :
  prtrace (close_step unv sts) = prtrace sts.  
Proof.
  assert (h:= close_step_is unv sts).
  assert (h0 := prtrace_app).
  destruct h as 
    [h1 | [h2 | [h3 | [h4 | [h5 | [h6 | [h7 | [h8 | [h9 | ]]]]]]]]].  
  - rewrite h1; rewrite h0;
    rewrite do_pairE_trace;
    apply app_nil_r.

  - rewrite h2; rewrite h0;
    rewrite do_encrE_trace;
    apply app_nil_r.
  - rewrite h3; rewrite h0;
    rewrite do_hashChck_trace;
    apply app_nil_r.
  - rewrite h4; rewrite h0;
    rewrite do_pairI_trace;
    apply app_nil_r.
  - rewrite h5; rewrite h0;
    rewrite do_encrI_trace;
    apply app_nil_r.
  - rewrite h6; rewrite h0;
    rewrite do_hashI_trace;
    apply app_nil_r.
  - rewrite h7; rewrite h0;
    rewrite do_qotChck_trace;
    apply app_nil_r.
  - rewrite h8; rewrite h0;
    rewrite do_sortChck_trace;
    apply app_nil_r.
  - rewrite h9; rewrite h0;
    rewrite do_sameChck_trace;
    apply app_nil_r.
  - rewrite H; rewrite h0;
    rewrite do_kyprChck_trace;
    apply app_nil_r.
Qed.

Proposition close_trace unv pr :
  prtrace (close unv pr) = prtrace pr.
Proof.
  unfold close.
  unfold close_steps_n.
  apply Iteration.pre_post.
  - unfold reflexive. 
    auto.
  - unfold transitive.
    intros. congruence.
  - intros. apply close_step_trace.
Qed.

Theorem saturate_trace unv pr pr' :
  saturate unv pr = SomeE pr' ->
  prtrace pr' =   prtrace pr.
Proof.
  intros H.
  apply sat_is_close in H.
  rewrite H.
  apply close_trace.
Qed. 

        
