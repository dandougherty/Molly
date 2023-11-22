(* Time-stamp: <Wed 11/22/23 11:02 Dan Dougherty Act.v>
*)

From Coq Require Import 
  Classical_Prop
  FunctionalExtensionality
  PropExtensionality
.

From RC Require Import
  CpdtTactics
  Utilities
  ListUtil
  Decidability
.

(** * Input, output and sending and receiving *)

Inductive Act (X: Type) :=
| Prm : X -> Act X
| Ret : X -> Act X
| Rcv  : X -> X -> Act X 
| Snd : X -> X -> Act X
.


(** Decidability *)

#[export] Instance eqDecision_act (X: Type) `{EqDecision X} : 
  EqDecision (Act X).
Proof.   
  intros x y.
  solve_decision.
Defined.

#[export] Instance eqDecision_acts (X: Type) `{EqDecision X} : 
  EqDecision (list (Act X)).
Proof.   
  intros x y.
  solve_decision.
  apply eqDecision_act. easy.
Defined.

#[export] Instance eqb_act (X: Type) `{EqbDec X} : 
  EqbDec (Act X).
Proof.   
apply eqDecisionEqbDec .
Defined.


(** ** Map a function into Act *)
Definition  Act_map 
  {X Y : Type} 
  (f :  X -> Y) 
  (iox : Act X) : (Act Y)
  := match iox with
     | Prm x => Prm (f x)
     | Ret x => Ret (f x)
     | Snd x1 x2 => Snd (f x1) (f x2)
     | Rcv x1 x2 => Rcv (f x1) (f x2)
     end.

Lemma Act_map_compose 
  {X Y Z : Type}
  (f: X -> Y)
  (g: Y -> Z) :
  Act_map (compose g f) = 
    compose (Act_map g) (Act_map f).
Proof.
  apply functional_extensionality.
  intros x;  destruct x; constructor; easy.
Qed.

(** ** Map a relation into Act *)

Inductive Act_mapR {X Y : Type} 
  (r : rel X Y) : rel (Act X) (Act Y)
  :=   
| Act_mapRPrm (x : X) (y: Y) :
  r x y  ->
  Act_mapR r (Prm x ) (Prm y)

| Act_mapRRet (x : X) (y: Y) :
  r x y  ->
  Act_mapR r (Ret x) (Ret y)

| Act_mapRSnd (x1 x2 : X) (y1 y2: Y) :
  r x1 y1 ->
  r x2 y2 ->
  Act_mapR r (Snd x1 x2) (Snd y1 y2)
           
| Act_mapRcv (x1 x2 : X) (y1 y2: Y) :
  r x1 y1 ->
  r x2 y2 ->
  Act_mapR r (Rcv x1 x2) (Rcv y1 y2).

(** Decidability *)

#[export] Instance Act_mapR_dec {X Y: Type}
  (r: rel X Y)
  {eq_dec: forall x y , Decision (r x y) }:
  forall (iox : Act X) (ioy: Act Y),
    (Decision (Act_mapR r iox ioy)).
Proof. intros iox ioy.
       unfold Decision.
       destruct iox eqn:ex.

       - destruct ioy eqn:ey.
         + destruct (decide (r x y)).
           * left; constructor; easy.
           * right; intros F; inv F; easy. 
         +  right; intros F; inv F.
         +  right; intros F; inv F.
         +  right; intros F; inv F.

       - destruct ioy eqn:ey.
         + right; intros F; inv F.
         + destruct (decide (r x y)) eqn:eqr.
           * left; constructor; easy.
           * right; intros F; inv F. congruence.
         +  right; intros F; inv F.
         +  right; intros F; inv F.

       -  destruct ioy eqn:ey.
          + right; intros F; inv F.
          + right; intros F; inv F.
          + destruct (decide (r x y));
              destruct (decide (r x0 y0)).
            * left; constructor; easy.
            * right; intros F; inv F; easy. 
            * right; intros F; inv F; easy. 
            * right; intros F; inv F; easy. 

          +  right; intros F; inv F; easy. 


       - destruct ioy eqn:ey.
         + destruct (decide (r x y)) eqn:er.
           * right; intros F; inv F; easy. 
           * right; intros F; inv F; easy. 
         +  right; intros F; inv F.
         +  right; intros F; inv F.
         +  destruct (decide (r x y)) eqn:er.
            destruct (decide (r x0 y0)).

           * left; constructor; easy.

           * right; intros F; inv F; easy. 
           * right; intros F; inv F; easy. 
Defined.

Lemma Act_mapR_mono
  {X Y : Type} (r r': rel X Y) xs ys :
  (forall x y, (r x y -> r' x y)) ->
  Act_mapR r xs ys ->
  Act_mapR r'  xs ys .
Proof.
  intros H0 H1.
  induction H1 .
  - constructor; apply H0 in H; easy.
  - constructor; apply H0 in H; easy.
  - constructor. apply H0 in H. easy.
    apply H0 in H1. easy.

  - constructor. apply H0 in H. easy.
    apply H0 in H1. easy.
Qed.


Lemma Act_mapR_iff
  {X Y : Type} (r r': rel X Y) xs ys :
  (forall x y, (r x y <-> r' x y)) ->
  Act_mapR r xs ys <->
  Act_mapR r'  xs ys .
Proof.
  intros .
  split.
  - apply Act_mapR_mono.
    apply H.
   - apply Act_mapR_mono.
    apply H.
Qed.


(* 
 We want this to be an equality, because we want to rewrite
with it.  Seem to have to detour through logical equivalence and
PropExtensionality.  *)


Lemma Act_mapR_equiv
  {X Y : Type} (r r': rel X Y) :
  (forall x y, (r x y <-> r' x y)) ->
  Act_mapR r  =
  Act_mapR r' .
Proof.
  intros .
apply functional_extensionality; intros e. 
apply functional_extensionality; intros d. 
apply propositional_extensionality.
apply Act_mapR_iff. easy.
Qed.


(** Lifting Act_map into Act_mapR *)

Lemma Act_mapR_map {X Y : Type} (f : X -> Y) x :
  Act_mapR (rel_of f) x (Act_map f x).
Proof.
  destruct x; constructor; easy.
Qed.


Lemma mapR_fun {X Y: Type} (f : X ->Y) es :
  forall ts,
    map (Act_map f) es = ts ->
    List_mapR (Act_mapR (rel_of f)) es ts.
Proof.
  induction es.
  - intros ts H. simpl in H. rewrite <- H. constructor.
  - intros ts H. simpl in H. rewrite <- H. 
    constructor.
    + apply Act_mapR_map.
    + apply IHes. easy.
Qed.



(** * Mapping and Composing *)

(** Act_mapRing is compatible with composition

 We want [compose_Act_mapRs], to be an equality, because we want to rewrite
with it.  Seem to have to detour through logical equivalence and
PropExtensionality. 

This is not innocent since it involves [propositional_extensionality]
 *)


Lemma compose_Act_mapRs_iff
  (T E V: Type) 
  (te: T -> E -> Prop) 
  (ev: E -> V -> Prop) 
  (a_t : Act T) (a_v: Act V) :
    Act_mapR (composeR te ev) a_t a_v <-> 
      composeR (Act_mapR te) (Act_mapR ev) a_t a_v.
 Proof. 
  split.
  - intros Hte. 
    inv Hte. 
    + inv H; clear H;
      exists (Prm y0);
      constructor; easy.

    + inv H; clear H;
      exists (Ret y0);
      constructor; easy.

    + inv H; clear H;
      inv H0; clear H0;
      exists (Snd y y0);
      constructor; easy.      

    + inv H; clear H;
      inv H0; clear H0;
      exists (Rcv y y0);
      constructor; easy.      

  - intros.
    inv H; clear H.
    inv H0; clear H0;
    inv H1; clear H1.
    + constructor; exists y0; easy.
    + constructor; exists y0; easy.
    + constructor. exists y1; easy.
      exists y2; easy .
    + constructor. exists y1; easy.
      exists y2; easy .
Qed.
    
Lemma compose_Act_mapRs 
  (T E V: Type) 
  (te: T -> E -> Prop)
  (ev: E -> V -> Prop) :
    Act_mapR (composeR te ev) = 
      composeR (Act_mapR te) (Act_mapR ev).
Proof.
apply functional_extensionality; intros e. 
apply functional_extensionality; intros r. 
apply propositional_extensionality.
apply compose_Act_mapRs_iff.
Qed.

