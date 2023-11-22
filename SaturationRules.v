(* Time-stamp: <Wed 11/22/23 11:30 Dan Dougherty SaturationRules.v>

TODO
- hodge podge of styles for firing rules.  ugh.

 *)

(**

1) Each Term constructor has rules for introduction and elimination.

 For example

We apply those rule as much as possible.: this is the function

[close : Terms -> Proc -> Proc]

the first argument to [close] is a "universe" of terms, in practice
this will be the set of subterms of the role we are compiling.

Being [closed] mean that we have closed under those rules

Theorem: (close pr) is closed.

2) A pr might be deficient because we were unable to do some
   eliminations, by not having enough decryption keys or bodies of
   hashes.

  This check is called being [justified].


3) Putting all that together, being [saturated_pr] is being closed  and justfied.


*)

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
  (* Iteration *)
  Act
  Sorts
  (* Runtime *)
  Term
  Role
  Proc
  SaturationClass
.
Open Scope string_scope.
Open Scope list_scope.


(** * Construction: Building a closed Proc *)

(** ** Eliminations *)

Definition is_pairE_redex
  (pr: Proc) (st: Stmt) : Prop := 
  match st with
    Bind ((Pr t1 t2),l) e => 
      (* ~ (is_pair_exp e) /\ *)
     (is_pair_expression_for pr (Pr t1 t2) e) = false /\
        (~ (term_exp_in_proc pr t1 (Frst l))
         \/ ~ (term_exp_in_proc pr t2 (Scnd l)))
  | _ => False
  end.
(**)
#[export] Instance pairE_redex_dec : 
  forall (pr: Proc) (smt: Stmt),
    (Decision (is_pairE_redex pr smt)).
Proof.
  intros pr smt.
  destruct smt as [[ t l] e | ev |  l1 l2 | l1 l2 |l1 l2 |  l s | ls | s].
  all: try (right; intros F; inv F).
  unfold is_pairE_redex.
  destruct t; apply _.
Defined.

(** [pr] acts the reference for "is a redex"; [wrklst] is the set of statements iterated over *)
Fixpoint pick_pairE_redex_help
  (pr: Proc) (wrklst: Stmts) : optionE Stmt :=
  match wrklst with 
  | [] => NoneE "no pairE redex"
  | st :: rest => 
      match (decide (is_pairE_redex pr st)) 
      with
      | left _ => SomeE st
      | right _ => pick_pairE_redex_help pr rest  
      end
end.

Definition pick_pairE_redex (pr : Proc) : optionE Stmt :=
  pick_pairE_redex_help pr pr.  

Lemma pick_pairE_redex_ok_help pr wrklst s :
  pick_pairE_redex_help pr wrklst = SomeE s ->
  In s wrklst /\
      is_pairE_redex pr s.
Proof.
  intros H.
  induction wrklst as [| frst rest IH]; simpl; auto.
  - inv H.
  - simpl in *.
    destruct_all_matches. inv H; subst.
    + split. now left. destruct_all_matches.
    + assert (h:= IH H). tauto.
Qed.

Lemma pick_pairE_redex_ok pr s :
  pick_pairE_redex pr = SomeE s ->
  In s pr /\
      is_pairE_redex pr s.
Proof.
  intros H.
  unfold pick_pairE_redex in *.
  now apply pick_pairE_redex_ok_help . 
Qed.

Definition fire_pairE
  (pr: Proc) (s : Stmt) : Stmts :=
  match s with
  | Bind ((Pr t1 t2) , l)  e =>  
      let (new1 , new2) := two_fresh_locs pr in 
      [Bind (t1,new1) (Frst l) ;
        Bind (t2,new2) (Scnd l)]

  | _ => []
  end.

(** This does no checking that the step is needed :
[is_pairE_redex] does that *)

Definition do_pairE (pr: Proc) : Stmts :=
  match pick_pairE_redex pr with
  | NoneE s => []
                
  | SomeE r => fire_pairE pr r
end.


Definition pairE_closed (pr: Proc) : Prop
  := forall (s: Stmt) ,
    In s pr ->  ~ (is_pairE_redex pr s).
(* *)
#[export] Instance pairE_closed_dec :
  forall (pr: Proc) ,
    (Decision (pairE_closed pr)).
Proof. 
  intros pr.
  apply list_forall_dec. intros.
  apply not_dec.
  apply _.
Defined.

 Lemma pairE_closed_then (pr : Proc) 
  : pairE_closed pr ->
    forall (t1 t2 : Term) (l: loc) (e : Expr),
      In (Bind ((Pr t1 t2),l) e) pr ->
      (is_pair_expression_for pr (Pr t1 t2) e) = true \/
      (* is_pair_exp e \/ *)
      ( (term_exp_in_proc pr t1 (Frst l)) 
        /\ (term_exp_in_proc pr t2 (Scnd l)) ) .
Proof.
  intros Hcl t1 t2 l e Hin.
  hnf in Hcl.
  specialize (Hcl (Bind (Pr t1 t2, l) e) Hin).
  unfold is_pairE_redex in Hcl.

  apply not_and_or in Hcl.
  destruct Hcl.  
  - left. now apply not_false_is_true.
  - tauto.
Qed.



(** *** Encryption Elimination , a.k.a. decryption *)

Definition is_encrE_redex
  (pr: Proc) (s2 : Stmt*Stmt) : Prop :=
  match s2 with 
  | ((Bind ((En tp tke), le) ee), 
      (Bind (tkd, lkd) ekd) )  =>
      (* ~ (is_encr_exp ee) /\ *)
      (is_encr_expression_for pr
           (En tp tke) ee) = false
      /\ are_inv tke tkd
      /\ ~ (term_exp_in_proc pr tp (Decr le lkd))

  | _ => False
  end.

#[export] Instance encrE_redex_dec : 
  forall (pr: Proc) (s2: Stmt*Stmt),
    (Decision (is_encrE_redex pr s2)).
Proof.
  intros pr s2.
  destruct s2 as [senc sdec_key].
  unfold is_encrE_redex. 
  destruct senc as [[ t l] e | ev | l1 l2| l1 l2| l1 l2 |  l s | l s| s]. 
  shelve.

  all: apply _.
  Unshelve.
  destruct t.
  all : try apply _.
  destruct sdec_key.
  all: apply _.
Defined.

Definition encrE_closed (pr: Proc) : Prop 
  := forall (p: Stmt*Stmt),
    In p (lsquare pr) -> 
    ~ (is_encrE_redex pr p).

Lemma encrE_closed_then (pr: Proc) : 
  encrE_closed pr ->
  forall (p k: Term) (le : loc) (ee: Expr),
    In (Bind ((En p k), le)  ee) pr ->
    (* ~ (is_encr_exp ee) -> *)
    (is_encr_expression_for pr (En p k) ee) = false ->

    forall (kd: Term) (lkd : loc) (ekd: Expr),
      In (Bind (kd, lkd) ekd) pr  ->
      are_inv k kd ->
      (term_exp_in_proc pr p (Decr le lkd)) .
Proof.
  intros.
  hnf in H.
  set (smt2:= (  (Bind (En p k, le) ee) ,
           (Bind (kd, lkd) ekd) )).
  assert (a: In smt2 (lsquare pr)).
  {apply in_prod.  easy. easy . }
  specialize (H smt2 a).
  apply NNPP.  intros F.
 assert (f: @is_encrE_redex pr smt2).
 - constructor; easy.
 - auto.
Qed.
(* *)
#[export] Instance encrE_closed_dec :
  forall  (pr: Proc) ,
    (Decision (encrE_closed pr)).
Proof.
  intros pr.
  apply list_forall_dec. intros.
  apply not_dec.
  apply encrE_redex_dec.
Defined.

Definition pick_encrE_redex 
  (pr: Proc):
  {stp: Stmt*Stmt | In stp (lsquare pr) /\ 
                    is_encrE_redex pr stp }
  +
    {forall stp, In stp (lsquare pr ) -> 
                 ~ is_encrE_redex  pr stp}.
Proof.
  destruct (list_sigma 
              (lsquare pr )
              (is_encrE_redex pr))
    as [E|E]; auto.
Defined.
  
(* This does no checking that the decryption is needed, or should
succeed; [is_encr_redex] does that *)

Definition fire_encrE
  (pr: Proc) (prems: Stmt*Stmt) : Stmts:=
  match prems with
  ((Bind ((En tp tke), le) ee), 
      (Bind (tkd, lkd) ekd))  =>
    let newl := fresh_loc pr in
    [Bind (tp, newl) (Decr le lkd)]


  | _ => []
  end.
 
(* Look for a redex, fire it and add to Proc if found, else
return pr. *)
 
Definition do_encrE (pr: Proc) : Stmts :=
  match pick_encrE_redex pr with
  | inleft x => fire_encrE pr (proj1_sig x)
                
  | inright _ => []
end.

(** ** Introductions *)

(** *** Pair Introduction *)
(* ====================== *)

(** The pair of terms named by [stp]
 - is in unv but
 - no location currently binds to it 
 *) 

(**  def redex *)

Definition is_pairI_redex 
  (unv: Terms) (pr: Proc) (opr: Stmt*Stmt) : Prop :=
  match opr with
  |  ( (Bind (t1, l1) _) , (Bind (t2, l2) _) ) =>
       In (Pr t1 t2) unv /\
         ~ (term_is_bound pr (Pr t1 t2))
  | _ => False 
  end.
(* *)
#[export] Instance pairI_redex_dec : 
  forall (unv: Terms) (pr: Proc) (p: Stmt*Stmt),
    (Decision (is_pairI_redex unv pr p)).
Proof. intros unv pr p.
       unfold Decision.

       destruct p as [smt1 smt2].
       destruct smt1. destruct t.
       destruct smt2. destruct t0.
       shelve.
       all: try (right; intros F; inv F).
       Unshelve.
       - unfold is_pairI_redex.
         destruct (decide (term_is_bound pr (Pr t t0))) eqn:e1.

         right. intros F. tauto.
         destruct (decide (In (Pr t t0) unv)).
         left. tauto.
         right. tauto.
Defined.

(** the negation *)

Definition pairI_closed
  (unv: Terms) (pr: Proc) : Prop
  := forall (p: Stmt*Stmt) ,
    In p (lsquare pr) ->
    ~ (is_pairI_redex unv pr p).
(* *)
#[export] Instance pairI_closed_dec :
  forall (unv: Terms) (pr: Proc) ,
    (Decision (pairI_closed unv pr)).
Proof.
  apply _.
Defined.

(**  computation *)

Definition pick_pairI_redexOLD
  (unv: Terms) (pr: Proc) :
  {stp: Stmt*Stmt | In stp (lsquare (pr)) /\ 
                      is_pairI_redex unv pr stp }
  +
    {forall stp, In stp (lsquare (pr)) -> 
                 ~    is_pairI_redex unv pr stp }.
Proof.
  destruct (list_sigma (lsquare (pr))
              (is_pairI_redex unv pr))
    as [E|E]; auto.
Defined.

(** Ultimately [prs] will be a list of ordere pairs from [pr]

Need to pass [pr] itself since need to consult [is_pairI_redex]
*)
Fixpoint pick_pairI_redex_help 
  (unv: Terms) (pr : Proc) 
  (prs: list (Stmt*Stmt)) : optionE (Stmt*Stmt) :=
  match prs with
  | [] => NoneE "no pairI redex "
  | opr :: rest =>
      match (decide (is_pairI_redex unv pr opr)) with
    | left _ => SomeE opr
    | right _ => pick_pairI_redex_help  unv pr rest
      end
  end.                              


Definition pick_pairI_redex 
  (unv: Terms) (pr: Proc) : optionE (Stmt*Stmt) :=
  pick_pairI_redex_help unv pr (lsquare pr).


(** This does no checking that the pair is needed; 
    [is_pairI_redex] does that *)

Definition fire_pairI  
  (pr: Proc) (stp: Stmt*Stmt) : Stmts :=
  match stp  with
  | ( (Bind (t1, l1) _) , (Bind (t2, l2) _) ) =>
      let newl := fresh_loc pr in
      [ Bind ((Pr t1 t2), newl) (Pair l1 l2)]
  | _ => []
  end.

(** alternative, just computing the increment.  
Maybe easier downstream? *)

Definition do_pairI 
  (unv: Terms) (pr: Proc) : Stmts :=
  match pick_pairI_redex unv pr with
  | NoneE s => []
                
  | SomeE r => fire_pairI pr r
end.
  

(** what we'll use *)

Lemma pairI_closed_then 
  (unv: Terms) (pr: Proc)  :
  pairI_closed unv pr -> 
  forall (t1 t2 : Term) l1 l2 e1 e2,
    In (Pr t1 t2) unv ->
    In (Bind (t1,l1) e1) pr -> 
    In (Bind (t2,l2) e2) pr -> 
    term_is_bound pr (Pr t1 t2) .
    (* exists l, In (Bind ((Pr t1 t2),l) (Pair l1 l2)) pr. *)
Proof.
  unfold pairI_closed.  
  intros H t1 t2 l1 l2 e1 e2 H0 H1 H2.
  assert (a:  In ( (Bind (t1,l1) e1) , (Bind (t2,l2) e2) )  (lsquare pr) ).
  { apply in_prod; easy. }
  specialize (H ( (Bind (t1,l1) e1) , (Bind (t2,l2) e2) ) a). 
  apply not_and_or in H; destruct H.
  - easy.
  - now apply NNPP in H. 
Qed.


(** *** Encr Introduction *)

(** def redex *)

Definition is_encrI_redex 
  (unv: Terms) (pr: Proc) (opr: Stmt*Stmt) : Prop :=
  match opr with
  |  ( (Bind (t1, l1) _) , (Bind (t2, l2) _) ) =>
       In (En t1 t2) unv /\
         ~ (term_is_bound pr (En t1 t2))
  | _ => False 
  end.
(* *)
#[export] Instance encrI_redex_dec : 
  forall (unv: Terms) (pr: Proc) (p: Stmt*Stmt),
    (Decision (is_encrI_redex unv pr p)).
Proof. intros unv pr p.
       unfold Decision.

       destruct p as [smt1 smt2].
       destruct smt1. destruct t.
       destruct smt2. destruct t0.
       shelve.
       all: try (right; intros F; inv F).
       Unshelve.
       - unfold is_encrI_redex.
         destruct (decide (term_is_bound pr (En t t0))) eqn:e1.

         right. intros F. tauto.
         destruct (decide (In (En t t0) unv)).
         left. tauto.
         right. tauto.
Defined.

(**  the negation *)

Definition encrI_closed
  (unv: Terms) (pr: Proc) : Prop
  := forall (p: Stmt*Stmt) ,
    In p (lsquare pr) ->
    ~ (is_encrI_redex unv pr p).
(* *)
#[export] Instance encrI_closed_dec :
  forall (unv: Terms) (pr: Proc) ,
    (Decision (encrI_closed unv pr)).
Proof.
  apply _.
Defined.

(** computation *)

(** Ultimately [prs] will be a list of ordered encrs from [pr]

Need to pass [pr] itself since need to consult [is_encrI_redex]
*)
Fixpoint pick_encrI_redex_help 
  (unv: Terms) (pr : Proc) 
  (prs: list (Stmt*Stmt)) : optionE (Stmt*Stmt) :=
  match prs with
  | [] => NoneE "no encrI redex "
  | opr :: rest =>
      match (decide (is_encrI_redex unv pr opr)) with
    | left _ => SomeE opr
    | right _ => pick_encrI_redex_help  unv pr rest
      end
  end.                              

Definition pick_encrI_redex 
  (unv: Terms) (pr: Proc) : optionE (Stmt*Stmt) :=
  pick_encrI_redex_help unv pr (lsquare pr).


(** This does no checking that the encr is needed; 
    [is_encrI_redex] does that *)

Definition fire_encrI  
  (pr: Proc) (stp: Stmt*Stmt) : Stmts :=
  match stp  with
  | ( (Bind (t1, l1) _) , (Bind (t2, l2) _) ) =>
      let newl := fresh_loc pr in
      [ Bind ((En t1 t2), newl) (Encr l1 l2)]
  | _ => []
  end.


Definition do_encrI
  (unv : Terms) (pr: Proc) : Proc :=
  match pick_encrI_redex unv pr with
    NoneE s => []
  | SomeE r => fire_encrI pr r
  end.


(** what we'll use *)

Lemma encrI_closed_then 
  (unv: Terms) (pr: Proc)  :
  encrI_closed unv pr -> 
  forall (t1 t2 : Term) l1 l2 e1 e2,
    In (En t1 t2) unv ->
    In (Bind (t1,l1) e1) pr -> 
    In (Bind (t2,l2) e2) pr -> 
    term_is_bound pr (En t1 t2) .
Proof.
  unfold encrI_closed.  
  intros H t1 t2 l1 l2 e1 e2 H0 H1 H2.
  assert (a:  In ( (Bind (t1,l1) e1) , (Bind (t2,l2) e2) )  (lsquare pr) ).
  { apply in_prod; easy. }
  specialize (H ( (Bind (t1,l1) e1) , (Bind (t2,l2) e2) ) a). 
  apply not_and_or in H; destruct H.
  - easy.
  - now apply NNPP in H. 
Qed.



(* ************************************************ *)
(* ** Hash *)
(* ************************************************ *)


(* ------------------------------------ *)
(** *** Hash Introduction *)
 
(** define redex *)

Definition is_hashI_redex 
  (unv: Terms) (pr: Proc) (smt: Stmt) : Prop :=
match smt with
|  (Bind (t, l) _) =>
     In (Hs t) unv /\
       ~ (term_is_bound pr (Hs t))
| _ => False 
end.

(* *)

#[export] Instance hashI_redex_dec : 
  forall (unv: Terms) (pr: Proc) (smt: Stmt),
    (Decision (is_hashI_redex unv pr smt)).
Proof. intros unv pr smt.
       unfold Decision.
       destruct smt as [[ t l] e | ev | l1 l2| l1 l2 | l1 l2 | l s |  l s |s]. 
       shelve.
       all: try (right; intros F; inv F).
       Unshelve. 
       unfold is_hashI_redex.
       destruct (decide (term_is_bound pr (Hs t))) eqn:e1.
       
         right. intros F. tauto.
         destruct (decide (In (Hs t) unv)).
         left. tauto.
         right. tauto.
Defined.

Definition hashI_closed 
  (unv: Terms) (pr: Proc) : Prop
  := forall (s: Stmt),
    In s pr ->
    ~ is_hashI_redex unv pr s.
(* *) 
#[export] Instance hashI_closed_dec :
  forall (unv: Terms) (pr: Proc) ,
    (Decision (hashI_closed unv pr)).
Proof.
  intros unv pr.
  apply _.
Defined.

(**  computation *)

Definition pick_hashI_redexOLD
  (unv: Terms) (pr: Proc) :
  {st: Stmt | In st pr /\ 
                is_hashI_redex unv pr st }
  +
    {forall st, In st pr -> 
                ~ is_hashI_redex unv pr st }.
Proof.
  destruct (list_sigma pr
              (is_hashI_redex unv pr))
    as [E|E]; auto.
Defined.

Fixpoint pick_hashI_redex 
  (unv: Terms) (pr: Proc) : optionE Stmt :=
  match pr with
    [] => NoneE "no hashI redex"
  | smt :: rest =>
    if (decide (is_hashI_redex unv pr smt))
    then SomeE smt
    else pick_hashI_redex  unv rest
  end.                              



(** This does no checking that the hash is needed; 
    [is_hashI_redex] does that *)

Definition fire_hashI  
  (pr: Proc) (st: Stmt) : Stmts :=
  match st  with
  | (Bind (t,l) e) =>
      let newl := fresh_loc pr in 
      [Bind ((Hs t), newl) (Hash l )]
  | _ => []
  end.

Definition do_hashI
  (unv : Terms) (pr: Proc) : Proc :=
  match pick_hashI_redex unv pr with
    NoneE s => []
  | SomeE r => fire_hashI pr r
  end.

(** what we'll use *)

Lemma hashI_closed_then
  (unv : Terms) (pr : Proc) :
  hashI_closed unv pr ->
  forall t l e,
    In (Hs t) unv ->
    In (Bind (t,l) e) pr ->
    term_is_bound pr (Hs t).
Proof.
  unfold hashI_closed.
  intros  H t l  e  H0 H1 .
  specialize (H (Bind (t,l) e) H1).

  unfold is_hashI_redex in H. 
  apply not_and_or in H; destruct H.
  - easy.
  - now apply NNPP in H. 
Qed.


(* ************************************************ *)
(* ** Quote *)
(* ************************************************ *)


(* ******************************************* *)
(** ** Checks *)
(* ******************************************* *)


(** *** Check Sort *)
(* ============== *)

(** define redex *)
    
Definition is_sortChck_redex
  (pr : list Stmt) (s: Stmt) : Prop :=
  match s with
  | (Bind (t,l) e) => 
      is_elementary t /\
        first_loc_forRb pr t l = true /\
        ~ (In (Csrt l (sort_of t)) pr)

  | _ => False
  end.
(* *)
#[export] Instance sortChck_redex_dec : 
  forall (pr: Proc) (s: Stmt),
    (Decision (is_sortChck_redex  pr s)).
Proof. intros pr s.
       unfold Decision.
       destruct s eqn:eqs.
       destruct t as [t l].
       shelve.
       all: right; easy.
       Unshelve.
       destruct (decide (is_elementary t)).
       - destruct (first_loc_forRb pr t l) eqn:eq1.
         + destruct (decide (In (Csrt l (sort_of t)) pr)).
          -- right; intros F; inv F. easy.
          -- left. easy. 
         + right; intros F; inv F. destruct H0; congruence. 
       - right; intros F; inv F; easy.
Defined.

(** negation *)

Definition sortChck_closed 
  (pr: Proc) : Prop
  := forall (s : Stmt),
    In s pr -> ~ is_sortChck_redex pr s.
    (* *)
#[export] Instance sortChck_closed_dec :
  forall (pr: Proc) ,
    (Decision (sortChck_closed pr)).
Proof.
  intros pr.
  apply list_forall_dec. intros.
  apply not_dec.
  apply sortChck_redex_dec.
Defined.

(**  what we'll use *)

(** uses a strong version of ax_sort_check, which is easier to prove
than ax_sort_check for the current implementation *)

Lemma strong_ax_sort_check (pr: Proc) : 
  sortChck_closed pr ->
  forall (t : Term)(l: loc) (e : Expr),
    is_elementary t ->
    In (Bind (t,l) e) pr ->
    exists l' e', 
      first_loc_for pr t = SomeE l' /\
      In (Bind (t,l') e') pr /\
        In (Csrt l' (sort_of t)) pr  .
Proof.
  intros Hcl t l e Helem Hin.
  assert (h0 := first_loc_for_intro pr t l e Hin).
  destruct h0 as [lfrst [e' [F1 F2]]].
  
  exists lfrst; exists e'.
  split; auto.
  split; auto.
  
  apply NNPP. intros F.
  assert (f: is_sortChck_redex pr (Bind (t,lfrst) e')).
  { constructor; auto. 
    split; auto. 
    unfold first_loc_forRb.
    destruct_all_matches.
    apply beq_rfl.
  }
  unfold sortChck_closed in *.
  unfold is_sortChck_redex in *.
  specialize (@Hcl (Bind (t,lfrst) e') F1);
    simpl in Hcl.
  tauto.
Qed.


Lemma sortChck_closed_sort_check 
  (pr: Proc) : 
  sortChck_closed pr ->
 ax_sort_check pr.
Proof. 
  intros Hcl t l e H2 H3 .

  assert (h:= @strong_ax_sort_check pr Hcl t l e H2 H3).
  destruct h as [l' [e' [P1 [P2 P3]]]].
  firstorder.
Qed.

Definition pick_sortChck_redex 
  (pr: list Stmt) :
  {b: Stmt | In b pr /\
               is_sortChck_redex pr b}
  +
    {forall b, In b pr -> 
                ~ is_sortChck_redex pr b }.
Proof.
  destruct (list_sigma pr
              (is_sortChck_redex pr ))
    as [E|E]; auto.
Defined.

Definition fire_sortChck
  (ts: list Stmt) (bd: Stmt) : Stmts :=
  match bd with
  | (Bind (t,l) e) => [Csrt l (sort_of t)]
  | _ => []
  end.

Definition do_sortChck
  (pr: Proc) :  Stmts := 
  match (pick_sortChck_redex pr) with
  | inleft x => fire_sortChck pr (proj1_sig x)
                
  | inright _ => []
end
.



 

(** *** Check Same *)
(* =============== *)

(** This formulation relies on the fact that 
if there is some first_loc for t then
first_loc_for_default, for any default, finds it *)

(** NB in the Csame statement we generate the first_loc binding comes
first *)

Definition is_sameChck_redex
(pr: Proc) (smt: Stmt) : Prop :=
  match smt with
  |  (Bind (t,l) e) =>
       is_elementary t /\
         (first_loc_forRb pr t l) = false  /\
         ~ (In (Csame 
                  (first_loc_for_default pr t)
                  l) pr)
  | _ => False
end .

#[export] Instance sameChck_redex_dec : 
  forall (pr: Proc) (st: Stmt),
    (Decision (is_sameChck_redex pr st)).
Proof.
  intros pr st.
  unfold Decision. unfold is_sameChck_redex.
  destruct st; auto.
  destruct t; auto.
  apply and_dec;  apply _.
Defined.

Definition pick_sameChck_redex
  (pr: Proc) :
  {st: Stmt | In st pr /\ 
                is_sameChck_redex pr st }
  +
    {forall st, In st pr -> 
                 ~ is_sameChck_redex pr st }.
Proof.
  destruct (list_sigma pr
              (is_sameChck_redex pr))
    as [E|E]; auto.
Defined.

Definition fire_sameChck  
  (pr: Proc) (st: Stmt) : Stmts :=
  match st  with
  |  (Bind (t,l) e)  =>
       [ (Csame  (first_loc_for_default pr t) l ) ]
  | _ => []
  end.

Definition do_sameChck
  (pr: Proc) :  Stmts :=
  match (pick_sameChck_redex pr) with
  | inleft x => fire_sameChck pr (proj1_sig x)
                
  | inright _ => []
end.


Definition sameChck_closed  
  (pr: Proc) : Prop
  := forall  (p: Stmt),
    In p ( pr) ->
    ~ (is_sameChck_redex pr p).
(* *)

#[export] Instance sameChck_closed_dec :
  forall (pr: Proc) ,
    (Decision (sameChck_closed pr)).
Proof.
  unfold Decision.
  intros pr.
  unfold sameChck_closed.
  apply list_forall_dec.
  intros.
  apply not_dec.
  apply sameChck_redex_dec.
Defined.


(**  Have to do some work to infer sameness from having 
[Csame] statements to first_locations
*)
Lemma sameChck_closed_then1 (pr: Proc) :
  sameChck_closed pr ->
  forall (t : Term) (lf l: loc) (ef e : Expr),
    is_elementary t ->
    In (Bind (t,lf) ef) pr ->
    In (Bind (t,l) e) pr ->
    first_loc_forRb pr t lf = true  ->
    first_loc_forRb pr t l = false   ->
    (In (Csame (first_loc_for_default pr t) l) pr)
.
Proof.
  unfold sameChck_closed.
  intros H t lf l ef e Helem  HBf Hbl Hflf Hfll.
  specialize (H (Bind (t,l) e) Hbl).
  unfold is_sameChck_redex in *.
  crush.
  apply NNPP in H; easy.
Qed.
 
Lemma not_false_true b :
  b <> false -> b = true.
Proof.
destruct b; auto.
Qed.


Lemma sameChck_closed_then (pr: Proc) :
  sameChck_closed pr ->
  forall (t : Term) (l1 l2: loc) (e1 e2 : Expr),
    is_elementary t ->
    In (Bind (t,l1) e1) pr ->
    In (Bind (t,l2) e2) pr ->
    same_linked pr l1 l2.
Proof.
intros H t l1 l2 e1 e2 Helem H1 H2 .
unfold sameChck_closed in H. 
assert (h1:= H (Bind (t, l1) e1) H1).
assert (h2:= H (Bind (t, l2) e2) H2).
unfold is_sameChck_redex in h1, h2.

apply not_and_or in h1,h2.
destruct h1 as [h11 | h12]; try easy.
destruct h2 as [h21 | h22]; try easy.
apply not_and_or in h12,h22.

destruct (decide (l1=l2)). 
- subst.
  apply Relation_Operators.rst_refl.

-
  destruct h12 as [hf1 | cs1]; destruct h22 as [hf2 | cs2].
  +  apply not_false_true in hf1.
     apply not_false_true in hf2.
     assert (hunq:= @first_locR_unique pr t l1 l2).
     assert (a3:= hunq hf1 hf2); easy.
 
  + (* hf1, cs2 *)
    apply NNPP in cs2. apply not_false_true in hf1.

    assert (z1: first_loc_forRb pr t l1 = true ->
                first_loc_for_default pr t = l1).
    { apply  (first_loc_forRb_default pr t l1) . }
    assert (a1:= z1 hf1).
    rewrite a1 in cs2.
    now apply Relation_Operators.rst_step. 
 
 + (* cs1, hf2 *)
   apply NNPP in cs1. apply not_false_true in hf2.
    assert (z2: first_loc_forRb pr t l2 = true ->
                first_loc_for_default pr t = l2).
    { apply  (first_loc_forRb_default pr t l2) . }
    assert (a2:= z2 hf2).
    rewrite a2 in cs1.
    apply Relation_Operators.rst_sym. 
    now apply Relation_Operators.rst_step. 

 + (* cs1, cs2 *)
   apply NNPP in cs1, cs2.
   apply Relation_Operators.rst_trans with 
     (first_loc_for_default pr t).
   -- apply Relation_Operators.rst_sym.
      eapply Relation_Operators.rst_step.
      apply cs1.
   -- eapply Relation_Operators.rst_step.
      apply cs2.
Qed.




(** ***  Check Quote  *)
(* =============================== *)

(**  define redex *)

(** would perhaps be better to just check 
against just ONE [t] Binding 
*)

Definition is_hashChck_redex 
  (pr: Proc) (smt2 : Stmt*Stmt) : Prop :=
  match smt2 with
    ( (Bind ((Hs t), lh) eh), 
      (Bind (t'    , lt) et) ) =>
    t = t'  
    (* /\ ~ is_hash_exp eh  *)
    /\ ~ (In (Chash lh lt) pr) 

| _ => False
end.
(* *)
#[export] Instance hashChck_redex_dec : 
  forall (pr: Proc) (p: Stmt*Stmt),
    (Decision (is_hashChck_redex pr p)).
Proof. intros  pr p. unfold Decision.
       destruct p. destruct s; destruct s0.
       unfold is_hashChck_redex.
       destruct t; destruct t0. destruct t.
       all: try (right; easy).

       apply and_dec. apply Term_eq_dec.
       (* apply and_dec. apply _. *)
       apply not_dec.
       apply list_in_dec.
       apply eqDecision_stmt.

       all: (right; intros F;  simpl in F; destruct t; destruct t; auto).
Defined.

(**  negation *)

Definition hashChck_closed 
  (pr: Proc) : Prop
  := forall (p: Stmt*Stmt),
    In p (lsquare pr) ->
    ~ is_hashChck_redex  pr p.
(* *) 
#[export] Instance hashChck_closed_dec :
  forall  (pr: Proc) ,
    (Decision (hashChck_closed pr)).
Proof.
  intros pr.
  apply list_forall_dec. intros.
  apply not_dec.
  apply hashChck_redex_dec.
Defined.
 
Lemma hashChck_closed_then (pr : Proc) :
  hashChck_closed pr ->
  forall t lh lt eh et,
    In (Bind ((Hs t), lh) eh) pr ->
    In (Bind (t    , lt) et) pr ->
    (* ~ is_hash_exp eh -> *)
    (In (Chash lh lt) pr) .
Proof.
  intros  H  t lh lt eh et H1 H3.  
  unfold hashChck_closed in H.
  set (p := ( (Bind ((Hs t), lh) eh) , 
              (Bind ( t ,    lt) et) )).
  assert (a: In p (lsquare pr)).
  { apply in_prod; easy. }
  specialize (H p a).
  apply NNPP. intros F.
  assert (f: is_hashChck_redex pr p).
  { constructor;  easy. }
  easy.
Qed.

Definition pick_hashChck_redex 
  (pr: Proc) :
  {stp: Stmt*Stmt | In stp (lsquare pr) /\ 
               is_hashChck_redex pr stp }
  +
    {forall stp, In stp (lsquare pr) -> 
                ~ is_hashChck_redex pr stp }.
Proof.
  destruct (list_sigma (lsquare pr)
              (is_hashChck_redex pr))
    as [E|E]; auto.
Defined.

Definition fire_hashChck  
  (pr: Proc) (stp: Stmt*Stmt) : Stmts :=
  match stp  with
  | ( (Bind ((Hs t), lh) eh) , 
      (Bind ( t' ,    lt) et) ) =>
    if (decide (t=t'))
    then [Chash lh lt]
    else []

  | _ => []
  end.

Definition do_hashChck
  (pr: Proc) :  Proc :=
  match (pick_hashChck_redex pr) with
  | inleft x => fire_hashChck pr (proj1_sig x)
                
  | inright _ => []
end.


(** *** Check Key Pair *)
(* ==================== *)

Equations is_kyprChck_redex
  : Proc -> (Stmt*Stmt) -> Prop :=
   
  is_kyprChck_redex pr
    ( (Bind ( t1,l1)  e1) , (Bind (t2,l2) e2) ) :=
    (makes_key_pair t1 t2 = true) /\
      (~ In (Ckypr l1 l2) pr) 
  ;
  
  is_kyprChck_redex pr 
    (_ , _) := False . 
(* *)
#[export] Instance kyprChck_redex_dec : 
  forall (pr: Proc) (p: Stmt*Stmt),
    (Decision (is_kyprChck_redex pr p)).
Proof.
  intros.
       apply FunctionalElimination_is_kyprChck_redex.
       shelve.
       all: right; easy.
       Unshelve. 
       intros.
       apply and_dec.
       apply bool_dec.  
       (* apply and_dec. *)
       apply not_dec; apply list_in_dec; apply eqDecision_stmt.
Defined.

Definition kyprChck_closed  
  (pr: Proc) : Prop
  := forall  (p: Stmt*Stmt),
    In p (lsquare pr) ->
    ~ (is_kyprChck_redex pr p).
(* *)
#[export]
Instance kyprChck_closed_dec :
  forall (pr: Proc) ,
    (Decision (kyprChck_closed pr)).
Proof.
  unfold Decision.
  intros pr.
  unfold kyprChck_closed.
  apply list_forall_dec.
  intros.
  apply not_dec.
  apply kyprChck_redex_dec.
Defined.

Lemma kyprChck_closed_then (pr: Proc) :
  kyprChck_closed pr ->
  forall (t1 t2: Term) l1 l2 e1 e2 ,
    makes_key_pair t1 t2 = true ->
    In (Bind (t1, l1)  e1) pr ->
    In (Bind (t2, l2)  e2) pr ->
    (In (Ckypr l1 l2) pr) .

Proof.
intros H t1 t2 l1 l2 e1 e2  Hp H1 H2.
unfold kyprChck_closed in H.
set (p :=  ( (Bind (t1,l1) e1) , (Bind (t2,l2) e2) )).
assert (a: In p (lsquare pr)).
    { apply in_prod; easy. }
specialize (H p a).

apply NNPP. intros F.

assert (f: is_kyprChck_redex pr p ).
{ constructor.  
  easy.
  auto. }
easy.
Qed.


Definition pick_kyprChck_redex 
  (pr: Proc) :
  {stp: Stmt*Stmt | In stp (lsquare (pr)) /\ 
                    is_kyprChck_redex pr stp }
  +
    {forall stp, In stp (lsquare (pr)) -> 
                 ~    is_kyprChck_redex pr stp }.
Proof.
  destruct (list_sigma (lsquare (pr))
              (is_kyprChck_redex pr))
    as [E|E]; auto.
Defined.


Definition fire_kyprChck  
  (pr: Proc) (stp: Stmt*Stmt) : Stmts :=
  match stp  with
  | ( (Bind (t1,l1) e1) , (Bind (t2,l2) e2) )  =>
      [ (Ckypr l1 l2)  ]
  | _ => []
  end.

Definition do_kyprChck
  (pr: Proc) :  Stmts :=
  match (pick_kyprChck_redex pr) with
  | inleft x => fire_kyprChck pr (proj1_sig x)
                
  | inright _ => []
end.


(** *** Check Quote *)
(* ============================== *)

Definition is_qotChck_redex 
  (pr: Proc) (smt : Stmt) : Prop :=
  match smt with
    (Bind ((Qt s),   l) e) =>
      (* ~ is_quote_exp e  *)
     ~ (In (Cquote l s) pr) 

| _ => False
end.


(* *)
#[export] Instance qotChck_redex_dec : 
  forall (pr: Proc) (p: Stmt),
    (Decision (is_qotChck_redex pr p)).
Proof. intros  pr p.
       unfold Decision.
       unfold is_qotChck_redex.
       destruct p.
       destruct t.
       all: try (right; easy).

       destruct t.
       all: try (right; easy).
       
       (* apply and_dec.  *)
       (* apply _. *)
       apply not_dec.       apply list_in_dec.
       apply eqDecision_stmt.
Defined.

(**  negation *)

Definition qotChck_closed 
  (pr: Proc) : Prop
  := forall (p: Stmt),
    In p pr ->
    ~ is_qotChck_redex  pr p.
(* *) 
#[export] Instance qotChck_closed_dec :
  forall  (pr: Proc) ,
    (Decision (qotChck_closed pr)).
Proof.
  intros pr.
  apply list_forall_dec. intros.
  apply not_dec.
  apply qotChck_redex_dec.
Defined.
 
(** what we'll use *)

Lemma qotChck_closed_then (pr : Proc) :
  qotChck_closed pr ->
  forall s l e  ,
    In (Bind ((Qt s), l)  e) pr ->
    (* ~ is_quote_exp e -> *)
    (In (Cquote l s) pr) .
Proof.
  intros  H s l e  H1.  
  unfold qotChck_closed in H.
  set (p := (Bind ((Qt s), l) e) ) .
  assert (a: In p pr).
  { easy. }
  (* { apply in_prod; easy. } *)
  specialize (H p a).

  apply NNPP. intros F.
  assert (f: is_qotChck_redex pr p).
  {  easy. }
  easy.
Qed.
        
(** computation *)

Definition pick_qotChck_redex 
  (pr: Proc) :
  {st: Stmt | In st pr /\
               is_qotChck_redex pr st }
  +
    {forall st, In st pr -> 
                ~ is_qotChck_redex pr st }.
Proof.
  destruct (list_sigma pr
              (is_qotChck_redex pr))
    as [E|E]; auto.
Defined.


(** This does no checking; 
    [is_qotChck_redex] does that *)

Definition fire_qotChck  
  (pr: Proc) (st: Stmt) : Stmts :=
  match st  with
  | (Bind ((Qt s),  l) e) =>  
    [Cquote l s]

  | _ => []
  end.

Definition do_qotChck
  (pr: Proc) :  Proc :=
match (pick_qotChck_redex pr) with
| inleft x => fire_qotChck pr (proj1_sig x)
| inright _ => []
end.


   
