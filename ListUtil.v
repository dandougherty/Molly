 (* Time-stamp: <Wed 11/22/23 12:16 Dan Dougherty ListUtil.v>

Some material is from Smolka and Brown library.
 *)


From Coq Require Import List Lia
  FunctionalExtensionality
  PropExtensionality.
Export ListNotations.


From RC Require Import
  Utilities
  Decidability
  CpdtTactics . 

Global Set Implicit Arguments. 
Global Unset Strict Implicit.

Open Scope list_scope.

(** ** Bounded sigma *)

(** Get an element of ls satisying g OR
    a proof that everything in ls satisfies ~g
 *)
Definition list_sigma X ls
  (g : X -> Prop) 
  (g_dec : forall x, Decision (g x)) :
  {x | In x ls /\ g x} + {forall x, In x ls -> ~ g x}.
Proof.
  induction ls as [ | x ls' IH]; simpl.
  - tauto.
  - destruct IH as [[y [D E]]|D].
    + eauto. 
    + destruct (g_dec x) as [E|E].
      * eauto.
      * right. intros y [[]|F]; auto. 
Defined.

Arguments list_sigma {X} ls g {g_dec}.


(** Perhaps  more reliable for computation than the decidable predicate [g] version *)

Definition list_sigma_bool X ls
  (b : X -> bool) :
  {x | In x ls /\ b x = true} + {forall x, In x ls -> b x = false}.
Proof.
  induction ls as [ | x ls' IH]; simpl.
  - tauto.
  - destruct IH as [[y [D E]]|D].
    + eauto. 
    + destruct (b x) eqn:E.
      * eauto.
      * right. intros y [[]|F]; auto. 
Defined.


Arguments list_sigma_bool {X} ls b .


(** Get a pair (x,y) with [g x = Some y]  OR 
    a proof that g x = None for all x in ls
 *)
Definition list_opt_sigma 
  X Y (ls: list X) 
  (g : X -> option Y) :
  { p | In (fst p) ls /\ 
          g (fst p) = Some (snd p)} + 
             {forall x, In x ls -> g x = None}.
Proof.
  induction ls as [ | x ls' IH]; simpl.
  - tauto.
  - destruct IH as [[y [D E]]|D].
    + eauto. 
    + destruct (g x) eqn:gx.
      * left.
        exists (x,y).
        simpl. tauto.
      * right. intros y [[]|F]; auto. 
Defined.

Arguments list_opt_sigma {X} {Y} ls g.


(* ========================== *)

(** ** Decidability for  Lists *)

(** These two use [list_sigma] just above *)

(** *** Universal quantification *)
#[export]
  Instance list_forall_dec X A (p : X -> Prop) (p_dec : forall x, Decision (p x)) :
  Decision (forall x, In x A -> p x).
Proof.
  destruct (list_sigma A (fun x => ~ p x)) as [[x [D E]]|D].
  - right. auto.
  - left. intros x E. apply dec_DN; auto.
Defined.

(** *** Existential quantification *)
#[export]
  Instance list_exists_dec X A (p : X -> Prop) (p_dec : forall x, Decision (p x)) :
  Decision (exists x, In x A /\ p x).
Proof.
  destruct (list_sigma A p) as [[x [D E]]|D].
  - left. eauto.
  - right. intros [x [E F]]. exact (D x E F).
Defined.

#[export]  Hint Unfold list_forall_dec list_exists_dec  : core.


(* -------------------------------------------------- *)

Definition equi X (A B : list X) : Prop :=
  incl A B /\ incl B A.

#[export]  Hint Unfold equi : core.

Notation "| A |" := (List.length A) (at level 65).
Notation "x 'el' A" := (In x A) (at level 70,  only parsing) .
Notation "A <<= B" := (incl A B) (at level 70).
Notation "A === B" := (equi A B) (at level 70).
Notation "A =/= B" := ((equi A B) -> False) (at level 70).

(* The following comments are for coqdoc *)
(** printing el #∊# *)
(** printing <<= #⊆# *)
(** printing === #≡# *)


Lemma incl_tl' {X:Type} (a: X) ls :  
  ls <<= a :: ls.
Proof. now apply incl_tl.
Qed.
 
(* A useful lemma *)

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (simpl; lia).
  apply C. now rewrite B.
Qed.

 
Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, Decision (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (list_sigma A p) as [F|F].
  + destruct F as [x F]. eauto.
  + contradiction (E F).
Qed.

(** @@ This must have an easier proof *)
Lemma list_exists X A  (p : X -> Prop) : 
  (forall x, Decision (p x)) ->
  ~ (forall x, x el A -> p x) -> exists x, x el A /\ ~ p x.
Proof. 
  intros HD H.
  set (np := (fun (x : X) => ~ (p x))).
  assert (npdec: (∀ x , Decision (np x))).
  { intros x.
    unfold Decision.
    destruct (decide (p x)) eqn:e.
    - right. auto.
    - left. auto. }
  assert (a:= @list_exists_DM X A np).
  apply a.
  apply npdec.
  enough ( ¬ (∀ x : X, In x A → p x)).
  - intros HF.
    firstorder.
  - apply H.
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, Decision (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (list_sigma A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Defined.

(** Membership

We use the following facts from the standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
 *)

#[export] Hint Resolve in_eq in_nil in_cons in_or_app : core.

Lemma in_sing X (x y : X) :
  x el [y] -> x = y.

Proof. simpl. intros [[]|[]]. reflexivity. Qed.

Lemma in_cons_neq X (x y : X) A :
  x el y::A -> x <> y -> x el A.

Proof. simpl. intros [[]|D] E; congruence. Qed.

Definition disjoint (X : Type) (A B : list X) :=
  ~ exists x, x el A /\ x el B.

Lemma disjoint_forall X (A B : list X) :
  disjoint A B <-> forall x, x el A -> ~ x el B.

Proof.
  split.
  - intros D x E F. apply D. exists x. auto.
  - intros D [x [E F]]. exact (D x E F).
Qed.

Lemma disjoint_cons X (x : X) A B :
  disjoint (x::A) B <-> ~ x el B /\ disjoint A B.

Proof.
  split.
  - intros D. split.
    + intros E. apply D. eauto.
    + intros [y [E F]]. apply D. eauto.
  - intros [D E] [y [[F|F] G]]. 
    + congruence.
    + apply E. eauto.
Qed.

(** StdLib [in_map_iff] is awkward as an iff *)
Lemma in_map_only_if:
  ∀ (A B : Type) (f : A → B) (l : list A) (y : B),
    In y (map f l) -> (∃ x : A, f x = y ∧ In x l).
Proof.
  apply in_map_iff.
Qed.


(** my map_opt *)

Fixpoint map_opt {A B} (f: A -> option B) (l: list A): list B :=
  match l with
  | [] =>  []
  | x :: xs =>
      match f x with
        None => map_opt f xs
      | Some y => y :: map_opt f xs
      end end.

(** A commutative diagram lemma involving mixed
[amp] and [map_opt]

draw the picture :-)
*)
Lemma map_map_opt_commute 
  {X Y X' Y' : Type} 
  (f: X -> Y)
  (f': X' -> Y')
  (g: X -> option X')
  (g': Y -> option Y')
  :
  (forall (x :X) (x': X') ,
      (g x = Some x')
      ->
        (g' (f x) = Some (f' x') ))
  ->
    (forall (x :X),
        (g x = None)
        ->
          (g' (f x) = None)
    )
  ->
    (forall x, 
        (compose (map_opt g') (map f)) x =
          (compose (map f')(map_opt g)) x).
Proof.
  intros H1 H2 xs.
  unfold compose.
  induction xs as [| x rest IH].
  - simpl; auto.
  - simpl.   
    destruct (g' (f x)) eqn:eq1.
    +  destruct (g x) eqn:eq2.
       -- specialize (H1 x x0 eq2).
          rewrite H1 in eq1.
          inv eq1.
          simpl. rewrite IH. easy. 
       -- specialize (H2 x eq2).
          rewrite H2 in eq1; inv eq1.
          
  + destruct (g x) eqn:eq2.
    -- specialize (H1 x x0 eq2).
          rewrite H1 in eq1.
          inv eq1.

    -- apply IH.
Qed.


Lemma in_map_opt_then:
  ∀ (A B : Type) 
    `{EqDecision B}
    (f : A -> option B) (l : list A) ,
  forall (y : B),
    In y (map_opt f l) ->
    exists x : A, In x l  /\ f x = Some y.
 Proof.
    intros A B Q f l . 
    induction l; simpl; auto.
    - firstorder.
    - intros b H.

      (* specialize (IHl b). *)
      destruct (decide ((f a) =  Some b)) eqn:e.
      + exists a. firstorder.
      + destruct (f a).
        * specialize (IHl b).
          assert (h: In b (map_opt f l)).
           { assert (hb : b <> b0).
             { congruence . }
             assert (hneq := in_cons_neq H hb); easy. }
          assert (h1:= IHl h).
          destruct h1 as [x [P1 P2]].
          exists x. tauto.
        * firstorder.
Qed.


(** Inclusion

We use the following facts from the standard library List.
- [A <<= B = forall y, x el A -> x el B]
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
 *)

#[export] Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app : core.

Lemma incl_nil X (A : list X) :
  nil <<= A.

Proof. intros x []. Qed.

#[export] Hint Resolve incl_nil : core.

Lemma incl_map X Y A B (f : X -> Y) :
  A <<= B -> map f A <<= map f B.

Proof.
  intros D y E. apply in_map_iff in E as [x [E E']].
  subst y. apply in_map_iff. eauto.
Qed.



Section Inclusion.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.

  Proof using Type.
    intros D. destruct A as [ |x A].
    - reflexivity.
    - exfalso. apply (D x). auto.
  Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.

  Proof using Type. intros D y E. destruct E; subst; auto. Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.

  Proof using Type. 
    split. 
    - intros D. split; hnf; auto.
    - intros [D E] z [F|F]; subst; auto.
  Qed.

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.

  Proof using Type. intros C D y E. destruct (C y E) as [F|F]. 
         congruence. apply F.
  Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.

  Proof using Type.
    intros C D y E.
    assert (F: y el x::B) by auto.
    destruct F as [F|F]; congruence.
  Qed.



End Inclusion.

#[export] Hint Resolve incl_shift : core.

Lemma incl_not {X:Type} (s1 s2: list X) (x: X) :
  s1 <<= s2 ->
  ~ In x s2 ->
  ~ In x s1.
Proof.
  unfold incl; intros; firstorder.
Qed.

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(** Setoid rewriting with list inclusion and list equivalence *)

#[export] Instance in_equi_proper X : 
  Proper (eq ==> @equi X ==> iff) (@In X).

Proof. hnf. intros x y []. hnf. firstorder. Defined.

#[export] Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).

Proof. hnf. intros x y D. hnf. firstorder. Defined.

#[export] Instance incl_preorder X : PreOrder (@incl X).

Proof. constructor; hnf; unfold incl; auto. Defined.

#[export] Instance equi_Equivalence X : Equivalence (@equi X).

Proof. constructor; hnf; firstorder. Defined.

#[export] Instance cons_equi_proper X : 
  Proper (eq ==> @equi X ==> @equi X) (@cons X).

Proof. hnf. intros x y []. hnf. firstorder. Defined.

#[export] Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).

Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Defined.


(** Equivalence *)

Section Equi.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === x::A.

  Proof using Type. auto. Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.

  Proof using Type. auto. Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.

  Proof using Type. split; intros z; simpl; tauto. Qed.

  Lemma equi_shift x A B :
    x::A++B === A++x::B.

  Proof using Type. 
    split; intros y.
    - intros [D|D].
      + subst; auto.
      + apply in_app_iff in D as [D|D]; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + destruct D; subst; auto.
  Qed.

  Lemma equi_rotate x A :
    x::A === A++[x].
  
  Proof using Type. 
    split; intros y; simpl.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
End Equi.




(** * Filterp *)

Definition filterp (X : Type) (p : X -> Prop) 
  (p_dec : forall x, Decision (p x)) : list X -> list X :=
  fix f A := match A with
             | nil => nil
             | x::A' => if decide (p x) then x :: f A' else f A'
             end.

Arguments filterp [X] p {p_dec} A.
(* # *)
Section FilterpLemmas.
  Variable X : Type.
  Variable p : X -> Prop.
  Context {p_dec : forall x, Decision (p x)}.

  Lemma in_filterp_iff x A :
    x el filterp p A <-> x el A /\ p x.
  
  Proof using Type. 
    induction A as [ |y A]; simpl.
    - tauto.
    - destruct (decide (p y)) as [B|B]; simpl;
        rewrite IHA; firstorder; subst; tauto.
  Qed.

  Lemma filterp_incl A :
    filterp p A <<= A.
  
  Proof using Type.
    intros x D. apply in_filterp_iff in D. apply D.
  Qed.

  Lemma filterp_mono A B :
    A <<= B -> filterp p A <<= filterp p B.

  Proof using Type.
    intros D x E. apply in_filterp_iff in E as [E E'].
    apply in_filterp_iff. auto.
  Qed.

  Lemma filterp_fst x A :
    p x -> filterp p (x::A) = x::filterp p A.
  Proof using Type.
    simpl. destruct (decide (p x)); tauto.
  Qed.

  Lemma filterp_app A B :
    filterp p (A ++ B) = filterp p A ++ filterp p B.
  Proof using Type.
    induction A as [ |y A]; simpl.
    - reflexivity.
    - rewrite IHA. destruct (decide (p y)); reflexivity.  
  Qed.

  Lemma filterp_fst' x A :
    ~ p x -> filterp p (x::A) = filterp p A.
  Proof using Type.
    simpl. destruct (decide (p x)); tauto.
  Qed.

End FilterpLemmas.

Section FilterpLemmas_pq.
  Variable X : Type.
  Variable p q : X -> Prop.
  Context {p_dec : forall x, Decision (p x)}.
  Context {q_dec : forall x, Decision (q x)}.

  Lemma filterp_pq_mono A :
    (forall x, x el A -> p x -> q x) -> filterp p A <<= filterp q A.

  Proof using Type. 
    intros D x E. apply in_filterp_iff in E as [E E'].
    apply in_filterp_iff. auto.
  Qed.

  Lemma filterp_pq_eq A :
    (forall x, x el A -> (p x <-> q x)) -> filterp p A = filterp q A.

  Proof using Type. 
    intros C; induction A as [ |x A]; simpl.
    - reflexivity.
    - destruct (decide (p x)) as [D|D]; destruct (decide (q x)) as [E|E].
      + f_equal. auto.
      + exfalso. apply E, (C x); auto.
      + exfalso. apply D, (C x); auto.
      + auto.
  Qed.

  Lemma filterp_and A :
    filterp p (filterp q A) = filterp (fun x => p x /\ q x) A.
  Proof using Type.
    set (r x := p x /\ q x).
    induction A as [ |x A]; simpl. reflexivity.
    destruct (decide (q x)) as [E|E]; simpl; rewrite IHA.
    - destruct (decide (p x)); destruct (decide (r x)); unfold r in *|-; auto; tauto. 
    - destruct (decide (r x)); unfold r in *|-; auto; tauto. 
  Qed.

End FilterpLemmas_pq.


Section FilterpComm.
  Variable X : Type.
  Variable p q : X -> Prop.
  Context {p_dec : forall x, Decision (p x)}.
  Context {q_dec : forall x, Decision (q x)}.

  Lemma filterp_comm A :
    filterp p (filterp q A) = filterp q (filterp p A).
  Proof using Type.
    do 2 rewrite filterp_and. apply filterp_pq_eq. tauto.
  Qed.

End FilterpComm.

(** * Element removal *)
Section Removal.
  Variable X : Type.
  Context {eq_X_dec : EqDecision X}.

  Definition rem (A : list X) (x : X) : list X :=
    filterp (fun z => ~ (z = x)) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof using Type.
    apply in_filterp_iff.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof using Type.
    intros D E. apply in_rem_iff in E. tauto.
  Qed.

  Lemma rem_incl A x :
    rem A x <<= A.
  Proof using Type.
    apply filterp_incl.
  Qed.

  Lemma rem_mono A B x :
    A <<= B -> rem A x <<= rem B x.
  Proof using Type.
    apply filterp_mono.
  Qed.

  Lemma rem_cons A B x :
    A <<= B -> rem (x::A) x <<= B.
  Proof using Type.
    intros E y F. apply E. apply in_rem_iff in F.
    destruct F as [[ | ]]; congruence.
  Qed.

  Lemma rem_cons' A B x y :
    x el B -> rem A y <<= B -> rem (x::A) y <<= B.
  Proof using Type.
    intros E F u G. 
    apply in_rem_iff in G as [[[]|G] H]. exact E.
    apply F. apply in_rem_iff. auto.
  Qed.

(* for some reason adding this into the core Hint datbase causes at leat one eauto to stacj overflow *)
  Lemma rem_in x y A :
    x el rem A y -> x el A.
  Proof using Type.
    apply rem_incl.
  Qed.

  Lemma rem_neq x y A :
    x <> y -> x el A -> x el rem A y.
  Proof using Type.
    intros E F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_app x A B :
    x el A -> B <<= A ++ rem B x.
  Proof using Type.
    intros E y F. destruct (decide (x=y)) as [[]| ];
      auto using rem_neq.
  Qed.

  Lemma rem_app' x A B C :
    rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
  Proof using Type.
    unfold rem; rewrite filterp_app; auto.
  Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof using Type.
    split; intros y; 
      intros [[]|E]; destruct (decide (x=y)) as [[]|D]; 
      eauto using rem_in, rem_neq. 
  Qed.

  Lemma rem_comm A x y :
    rem (rem A x) y = rem (rem A y) x.
  Proof using Type.
    apply filterp_comm.
  Qed.

  Lemma rem_fst x A :
    rem (x::A) x = rem A x.
  Proof using Type.
    unfold rem. rewrite filterp_fst'; auto.
  Qed.

  Lemma rem_fst' x y A :
    x <> y -> rem (x::A) y = x::rem A y.
  Proof using Type.
    intros E. unfold rem. rewrite filterp_fst; auto.
  Qed.

End Removal.




#[export] Hint Resolve 
  rem_not_in 
  rem_incl 
  rem_mono 
  rem_cons 
  rem_cons'
  rem_app
  rem_app'
    rem_neq
    (* rem_in *)
  : core.


(** * Duplicate-free lists *)

(** @@ NOTE *)

(* Cf stdlib [nodup]
Inductive dupfree (X : Type) : list X -> Prop :=
| dupfreeN : dupfree nil
| dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).

Cf stdlib [NoDup]
Inductive NoDup (A : Type) : list A → Prop :=
    NoDup_nil : NoDup []
  | NoDup_cons : ∀ (x : A) (l : list A), ¬ In x l → NoDup l → NoDup (x :: l).
*)

Section Dupfree.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma NoDup_inv x A :
    NoDup (x::A) <-> ~ x el A /\ NoDup A.
  Proof using Type. 
    split; intros D.
    - inversion D; auto.
    - apply NoDup_cons; tauto.
  Qed.

  Lemma NoDup_app A B :
    disjoint A B -> NoDup A -> NoDup B -> NoDup (A++B).

  Proof using Type.
    intros D E F. induction E as [ |x A E' E]; simpl.
    - exact F.
    -  apply disjoint_cons in D as [D D'].
       constructor; [ |exact (IHE D')].
       intros G. apply in_app_iff in G; tauto.
  Qed.

  Lemma NoDup_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) -> 
    NoDup A -> NoDup (map f A).

  Proof using Type.
    intros D E. induction E as [ |x A E' E]; simpl.
    - constructor. 
    - 
      constructor;
        [ |now auto].
      
      intros F. apply in_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma NoDup_filterp p (p_dec : forall x, Decision (p x)) A :
    NoDup A -> NoDup (filterp p A).

  Proof using Type.
    intros D. induction D as [ |x A C D]; simpl.
    - left.
    - destruct (decide (p x)) as [E|E]; [ |exact IHD].
      right; [ |exact IHD].
      intros F. apply C. apply filterp_incl in F. exact F.
  Qed.


  Lemma NoDup_dec A :
    EqDecision X -> Decision (NoDup A).

  Proof using Type.
    intros D. induction A as [ |x A].
    - left. left.
    - destruct (decide (x el A)) as [E|E].
      + right. intros F. inversion F; tauto.
      + destruct (IHA) as [F|F].
        -- left. now apply NoDup_cons.
        -- right. intros HF. 
           now apply NoDup_cons_iff in HF.
  Qed.


End Dupfree.


Section Undup.
  Variable X : Type.
  Context {eq_X_dec : EqDecision X}.
  Implicit Types A B : list X.

  

  Fixpoint undup (A : list X) : list X :=
    match A with
    | nil => nil
    | x::A' => if decide (x el A') then undup A' else  x :: undup A'
    end.

  Lemma undup_fp_equi A :
    undup A === A.
  Proof using Type.
    induction A as [ |x A]; simpl.
    - reflexivity.
    - destruct (decide (x el A)) as [E|E]; rewrite IHA; auto.
  Qed.

  Lemma NoDup_undup A :
    NoDup (undup A).
  Proof using Type.
    induction A as [ |x A]; simpl.
    - left.
    - destruct (decide (x el A)) as [E|E]; auto.
      right; auto. now rewrite undup_fp_equi. 
  Qed.

  Lemma undup_incl A B :
    A <<= B <-> undup A <<= undup B.
  Proof using Type.
    now do 2 rewrite undup_fp_equi.
  Qed.

  Lemma undup_equi A B :
    A === B <-> undup A === undup B.
  Proof using Type.
    now do 2 rewrite undup_fp_equi.
  Qed.

  Lemma undup_eq A :
    NoDup A -> undup A = A.
  Proof using Type.
    intros E. induction E as [ |x A E F]; simpl.
    - reflexivity.
    - rewrite IHF. destruct (decide (x el A)) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent A :
    undup (undup A) = undup A.

  Proof using Type. apply undup_eq, NoDup_undup. Qed.

End Undup.

Section DupfreeLength.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma NoDup_reorder A x :
    NoDup A -> x el A -> 
    exists A', A === x::A' /\ |A'| < |A| /\ NoDup (x::A').

  Proof using Type.
    intros E. revert x. induction E as [ |y A H]; intros x F.
    - contradiction F.
    - destruct F as [F|F].
      + subst y. exists A. auto using NoDup. 
      + specialize (IHE x F). destruct IHE as [A' [G [K1 K2]]].
        exists (y::A'). split; [ |split].
        * rewrite G. apply equi_swap.
        * simpl. lia.
        * { apply NoDup_inv in K2 as [K2 K3]. right. 
            - intros [M|M]; subst; auto.
            - right; [ |exact K3].
              intros M; apply H. apply G. auto. }
  Qed.

  Lemma NoDup_le A B :
    NoDup A -> NoDup B -> A <<= B -> |A| <= |B|.

  Proof using Type. 
    intros E; revert B.
    induction A as [ |x A]; simpl; intros B F G.
    - lia.
    - apply incl_lcons in G as [G H]. 
      destruct (NoDup_reorder F G) as [B' [K [L M]]].
      apply NoDup_inv in E as [E1 E2].
      apply NoDup_inv in M as [M1 M2].
      cut (A <<= B').
      { intros N. specialize (IHA E2 B' M2 N). lia. }
      apply incl_rcons with (x:=x); [ |exact E1].
      rewrite H. apply K.
  Qed.

  Lemma NoDup_eq A B :
    NoDup A -> NoDup B -> A === B -> |A|=|B|.

  Proof using Type. 
    intros D E [F G]. 
    apply (NoDup_le D E) in F. 
    apply (NoDup_le E D) in G. 
    lia.
  Qed.

  Lemma NoDup_lt A B x :
    NoDup A -> NoDup B -> A <<= B -> 
    x el B -> ~ x el A  -> |A| < |B|.

  Proof using Type.
    intros E F G H K.
    destruct (NoDup_reorder F H) as [B' [L [M N]]].
    rewrite (NoDup_eq F N L). 
    cut (|A|<=|B'|). { simpl; lia. }
    apply NoDup_le.
    - exact E.
    - now inversion N.
    - apply incl_rcons with (x:=x).
      + rewrite G. apply  L.
      + exact K.
  Qed.

(* Stack overflow here *)
  Lemma NoDup_ex A B :
    EqDecision X -> 
    NoDup A -> 
    NoDup B -> 
  |A| < |B| -> 
 (exists x, In x B /\ ~ (In x A)).
  Proof using Type.
    intros D E F H.
    destruct (list_sigma B (fun x => ~ x el A)) as [[x K]|K].
    - exists x; exact K.
    - exfalso. 
      assert (L : B <<= A).
      { 
        intros x L. 
         apply dec_DN; auto.
        (* Print Hint. *)
        (* unfold Decision. *)
        now apply list_in_dec. }
      apply NoDup_le in L; auto; lia.
  Qed.

  Lemma NoDup_equi A B :
    EqDecision X -> NoDup A -> NoDup B -> A <<= B -> |A|=|B| -> A === B.

  Proof using Type.
    intros C D E F G. split. exact F.
    destruct (list_sigma B (fun x => ~ x el A)) as [[x [H K]]|H].
    - exfalso. assert (L:=NoDup_lt D E F H K). lia.
    - intros x L. apply dec_DN; auto. now apply list_in_dec.
  Qed.

End DupfreeLength.

(** * Cardinality *)

Section Cardinality.
  Variable X : Type.
  Context {eq_X_dec : EqDecision X}.
  Implicit Types A B : list X.

  Definition card (A : list X) : nat := |undup A|.

  Lemma card_le A B :
    A <<= B -> card A <= card B.

  Proof using Type.
    intros E. apply NoDup_le.
    - apply NoDup_undup. 
    - apply NoDup_undup.
    - apply undup_incl, E.
  Qed.

  Lemma card_eq A B :
    A === B -> card A = card B.

  Proof using Type.
    intros [E F]. apply card_le in E. apply card_le in F. lia.
  Qed.

  Lemma card_equi A B :
    A <<= B -> card A = card B -> A === B.
  Proof using Type.
    intros D E.
    apply <- undup_equi. apply -> undup_incl in D.
    apply NoDup_equi; auto using NoDup_undup.    
  Qed.

  Lemma card_lt A B x :
    A <<= B -> x el B -> ~ x el A -> card A < card B.

  Proof using Type.
    intros D E F.
    apply (NoDup_lt (A:= undup A) (B:= undup B) (x:=x)).
    - apply NoDup_undup.
    - apply NoDup_undup.
    - apply undup_incl, D.
    - apply undup_fp_equi, E.
    - rewrite undup_fp_equi. exact F.
  Qed.

  Lemma card_or A B :
    A <<= B -> A === B \/ card A < card B.

  Proof using Type.
    intros D.
    destruct (decide (card A = card B)) as [F|F].
    - left. apply card_equi; auto.
    - right. apply card_le in D. lia.
  Qed.

  Lemma card_ex A B :
    card A < card B -> exists x, x el B /\ ~ x el A.

  Proof using Type.
    intros E.
    destruct (NoDup_ex (A:=undup A) (B:=undup B)) as [x F].
    - exact eq_X_dec.
    - apply NoDup_undup.
    - apply NoDup_undup.
    - exact E.
    - exists x. setoid_rewrite undup_fp_equi in F. exact F.
      (*Coq bug: Must use setoid_rewrite here *)
  Qed.

  Lemma card_cons x A :
    card (x::A) = if decide (x el A) then card A else 1 + card A.
  Proof using Type.
    unfold card at 1; simpl. now destruct (decide (In x A)).
  Qed.

  Lemma card_cons_rem x A :
    card (x::A) = 1 + card (rem A x).
  Proof using Type.
    rewrite (card_eq (rem_equi x A)). 
    rewrite card_cons.
    destruct (decide (x el rem A x)) as [D|D].
    - apply in_rem_iff in D; tauto.
    - reflexivity.
  Qed.

  Lemma card_0 A :
    card A = 0 -> A = nil.
  Proof using Type.
    destruct A as [ |x A]; intros D.
    - reflexivity.
    - exfalso. rewrite card_cons_rem in D. lia.
  Qed.

End Cardinality.

#[export] Instance card_equi_proper X (D: EqDecision X) : 
  Proper (@equi X ==> eq) (@card X D).
Proof. 
  hnf. apply card_eq.
Defined.

(** Pairs from lists *)


(** All pairs of elements, in either order, from [ls1] and [ls2] *)
Definition pairs {X: Type} (ls1 ls2 : list X) : list (X * X) :=
  list_prod ls1 ls2 ++   list_prod ls2 ls1.

(** * Power lists *)

Section PowerRep.
  Variable X : Type.
  Context {eq_X_dec : EqDecision X}.

  Fixpoint power (U : list X ) : list (list X) :=
    match U with
    | nil => [nil]
    | x :: U' => power U' ++ map (cons x) (power U')
    end.
  
  Lemma power_incl A U :
    A el power U -> A <<= U.

  Proof using Type.
    revert A; induction U as [ |x U]; simpl; intros A D.
    - destruct D as [[]|[]]; auto.
    - apply in_app_iff in D as [E|E]. now auto.
      apply in_map_iff in E as [A' [E F]]. subst A.
      apply incl_shift. auto.
  Qed.

  Lemma power_nil U :
    nil el power U.

  Proof using Type. induction U; simpl; auto. Qed.

  Definition rep (A U : list X) : list X :=
    filterp (fun x => x el A) U.

  Lemma rep_power A U :
    rep A U el power U.

  Proof using Type.
    revert A; induction U as [ |x U]; intros A.
    - simpl; auto.
    - simpl. destruct (decide (x el A)) as [D|D]; auto using in_map.
  Qed.

  Lemma rep_incl A U :
    rep A U <<= A.

  Proof using Type.
    unfold rep. intros x D. apply in_filterp_iff in D. apply D.
  Qed.

  Lemma rep_in x A U :
    A <<= U -> x el A -> x el rep A U.
  Proof using Type.
    intros D E. apply in_filterp_iff; auto.
  Qed.

  Lemma rep_equi A U :
    A <<= U -> rep A U === A.

  Proof using Type.
    intros D. split. now apply rep_incl.
    intros x. apply rep_in, D.
  Qed.

  Lemma rep_mono A B U :
    A <<= B -> rep A U <<= rep B U.

  Proof using Type. intros D. apply filterp_pq_mono. auto. Qed.

  Lemma rep_eq' A B U :
    (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.

  Proof using Type. intros D. apply filterp_pq_eq. auto. Qed.

  Lemma rep_eq A B U :
    A === B -> rep A U = rep B U.

  Proof using Type. intros D. apply filterp_pq_eq. firstorder. Qed.

  Lemma rep_injective A B U :
    A <<= U -> B <<= U -> rep A U = rep B U -> A === B.

  Proof using Type.
    intros D E F. transitivity (rep A U). 
    - symmetry. apply rep_equi, D.
    - rewrite F. apply rep_equi, E.
  Qed.

  Lemma rep_idempotent A U :
    rep (rep A U) U = rep A U.

  Proof using Type. 
    unfold rep at 1 3. apply filterp_pq_eq.
    intros x D. split.
    + apply rep_incl.
    + intros E. apply in_filterp_iff. auto.
  Qed.

  Lemma NoDup_power U :
    NoDup U -> NoDup (power U).

  Proof using Type.
    intros D. induction D as [ |x U E D]; simpl.
    - constructor. now auto. constructor.
    - apply NoDup_app.
      + intros [A [F G]]. apply in_map_iff in G as [A' [G G']].
        subst A. apply E. apply (power_incl F). auto.
      + exact IHD.
      + apply NoDup_map; congruence.
  Qed.

  Lemma NoDup_in_power U A :
    A el power U -> NoDup U -> NoDup A.

  Proof using Type.
    intros E D. revert A E.
    induction D as [ |x U D D']; simpl; intros A E.
    - destruct E as [[]|[]]. constructor.
    - apply in_app_iff in E as [E|E].
      + auto.
      + apply in_map_iff in E as [A' [E E']]. subst A.
        constructor.
        * intros F; apply D. apply (power_incl E'), F.
        * auto.
  Qed.

  Lemma rep_NoDup A U :
    NoDup U -> A el power U -> rep A U = A.

  Proof using Type.
    intros D; revert A. 
    induction D as [ |x U E F]; intros A G.
    - destruct G as [[]|[]]; reflexivity.
    - simpl in G. apply in_app_iff in G as [G|G]. 
      + simpl. destruct (decide (x el A)) as [H|H].
        * exfalso. apply E. apply (power_incl G), H.
        * auto.
      + apply in_map_iff in G as [A' [G H]]. subst A.
        simpl. destruct (decide (x=x \/ x el A')) as [G|G].
        * f_equal. rewrite <- (IHF A' H) at 2.
          apply filterp_pq_eq. apply power_incl in H.
          intros z K. split; [ |now auto]. 
          intros [L|L]; subst; tauto.
        * exfalso; auto.
  Qed.

  Lemma power_extensional A B U :
    NoDup U -> A el power U -> B el power U -> A === B -> A = B.

  Proof using eq_X_dec.
    intros D E F G. 
    rewrite <- (rep_NoDup D E). rewrite <- (rep_NoDup D F).
    apply rep_eq, G.
  Qed.

End PowerRep.


Lemma complete_induction (p : nat -> Prop) (x : nat) :
  (forall x, (forall y, y<x -> p y) -> p x) -> p x.

Proof. intros A. apply A. induction x ; intros y B.
       exfalso ; lia.
       apply A. intros z C. apply IHx. lia. Qed.

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.

Proof. 
  intros IH x. apply IH. 
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. lia.
    - intros y B. apply IH. intros z C. apply IHn. lia. }
  apply G.
Qed.

Section pos.
   
  (* Definition elAt := nth_error. *)
  (* Notation "A '.[' i  ']'" := (elAt A i) (no associativity, at level 50). *)

  Variable X:Type.
  Context {Eq_dec:EqDecision X}.
  
  Fixpoint pos (s : X) (A : list X) : option nat :=
    match A with
    | nil => None
    | a :: A => if decide (s = a) 
                then Some 0 
                else match pos s A with 
                       None => None 
                     | Some n => Some (S n) 
                     end
    end.

  Lemma el_pos s A : s el A -> exists m, pos s A = Some m.
  Proof using Type.
    revert s; induction A; simpl; intros s H.
    - contradiction.
    - destruct (decide (s = a)) as [D | D]; eauto; 
        destruct H; try congruence.
      destruct (IHA s H) as [n Hn]; eexists; now rewrite Hn.
  Qed.
  
  Lemma pos_elAt s A i : pos s A = Some i -> nth_error A i = Some s.
  Proof using Type.
    revert i s. induction A; intros i s.
    - destruct i; inversion 1.
    - simpl. destruct (decide (s = a)).
      + inversion 1; subst; reflexivity.
      + destruct i; destruct (pos s A) eqn:B; inversion 1; subst; eauto. 
  Qed.

  Lemma elAt_el  A (s : X) m : nth_error A m = Some s -> s el A.
  Proof using Type.
    revert A. induction m; intros []; inversion 1; eauto.
  Qed.
  
  Lemma el_elAt (s : X) A : s el A -> exists m, nth_error A m = Some s.
  Proof using Eq_dec.
    intros H; destruct (el_pos H);  eexists; eauto using pos_elAt.
  Qed.


Lemma elAt_app (A : list X) i B s : 
  nth_error A i = Some s -> nth_error (A ++ B) i = Some s.
Proof using Type.
  revert s B i. induction A; intros s B i H; destruct i; simpl; firstorder; inversion H.
Qed.
  

  Lemma nth_error_none A n l : nth_error l n = @None A -> List.length l <= n.
  Proof using Type. revert n;
           induction l; intros n.
         - simpl; lia.
         - simpl. intros. destruct n. inversion H. inversion H. assert (| l | <= n). eauto. lia.
  Qed.


(* --------------------- *)
(**  [nth] and [pos] functions that act as inverses *)

Definition nth_def  (n: nat) (xs: list X) (defX: X): X :=
  match nth_error xs n with 
    | None => defX
    | Some x => x
  end.

Definition pos_def (x:X) (A : list X) (defnat: nat) : nat :=
  match pos x A with
    None => defnat
  | Some n => n
  end.

(** nth_def is a left inverse for pos_def, no matter what the defaults are *)

Lemma nth_pos (defX: X) (defnat: nat) (s : X) A : 
  s el A -> nth_def (pos_def s A defnat) A defX = s.
Proof using Eq_dec.
  intros H; destruct (el_pos H).  
  assert (h: pos_def s A defnat = x).
  { unfold pos_def. rewrite H0. easy. }
  rewrite h.
  unfold nth_def.
  assert (h1:= @pos_elAt s A x H0).
  now rewrite h1.
Qed.

(* --------------------- *)


End pos.

Arguments pos {_} {_} _ _.
Arguments el_elAt {_} {_} {_} _ _.


(* ================= *)
(** [map_filter] *)
(* ================= *)

Section map_filter.

  Open Scope list_scope.

  Definition is_Someb {A: Type} (o : option A) : bool :=
    match o with
      Some _ => true
    | None => false
    end.

  Fixpoint just_Somes {B : Type} (l: list (option B)) : list B :=
    match l with 
      [] => []
    | None :: rest => just_Somes rest
    | (Some a) :: rest => a :: just_Somes rest
    end.

  Definition map_filter {A B : Type} (f: A -> option B) (l: list A) : list B :=
    just_Somes (map f l).

  Lemma just_Somes_In' {A: Type} (l : list (option A)) y :
    In (Some y) l ->
    In y (just_Somes l).
  Proof.
    intros H.
    induction l as [ | a rest IH].
    - inversion H.
    - destruct H.
      + subst.
        simpl. now left.
      + apply IH in H.
        destruct a eqn: ae.
        --  simpl. now right.
        -- simpl. assumption.
  Qed.

  Lemma just_Somes_In'' {A: Type} (l : list (option A)) y :
    In y (just_Somes l) -> In (Some y) l .
  Proof.
    intros H.
    induction l as [ | a rest IH].
    - inversion H.
    - simpl in H.
      destruct a eqn:e.
      + apply in_inv in H; destruct H; subst.
        -- auto.
        -- apply IH in H.
           auto.
      + apply IH in H.
        auto.
  Qed.

  Proposition just_Somes_In {A: Type} (l : list (option A)) y :
    In y (just_Somes l) <-> In (Some y) l .
  Proof.
    assert (a1:= @just_Somes_In' A l).
    assert (a2:= @just_Somes_In'' A l).
    firstorder.
  Qed.


  Lemma if_map_filter :
    forall (A B : Type) (f : A -> option B) (l : list A)  (y : B), 
      In y (map_filter f l) -> exists (x:A), In x l /\ f x = Some y.
  Proof.
    unfold map_filter;
      intros A B f l y H;
      apply just_Somes_In in H;
      apply in_map_iff in H;
      destruct H as [x E]; now exists x.
  Qed.

  Lemma then_map_filter' 
    {A B : Type} (f : A -> option B) (l : list A)  (y : B) :
    (exists (x: A), In x l /\ f x = Some y) -> In y (map_filter f l).
  Proof.
    intros H;
      apply just_Somes_In;
      apply in_map_iff;
      destruct H as [x E]; now exists x.
  Qed.

  (** NB this is more convenient to use than the version with an
existential in the hypothesis.)  *)
  Lemma then_map_filter 
    {A B : Type} (f : A -> option B) (l : list A) (x:A) (y : B) :
    (In x l /\ f x = Some y) -> In y (map_filter f l).
  Proof.
    intros H.
    apply just_Somes_In.
    apply in_map_iff.
    now exists x.
  Qed.

  (** The main result about [map_filter] 
   *)
  Proposition map_filter_char {A B: Type}
    (f : A -> option B) (l : list A)  (y : B): 
    In y (map_filter f l)  <-> exists (x: A), In x l /\ f x = Some y.
  Proof.
    split.
    - apply if_map_filter.
    - intros. destruct H as [x E]; now apply then_map_filter with x.
  Qed.

  Lemma just_Somes_app {B: Type} (l l' : list (option B)) :
    just_Somes (l ++ l') = (just_Somes l) ++ (just_Somes l').
  Proof.
    induction l as [ | x rest IH].
    - reflexivity. 
    - simpl.
      destruct x eqn:e; now rewrite IH.
  Qed.

  Lemma map_filter_app {A B: Type}  (f : A -> option B) (l l' : list A) :
    map_filter f (l ++ l') = map_filter f l ++ map_filter f l'.
  Proof.
    unfold map_filter.
    rewrite map_app.
    apply just_Somes_app.
  Qed.

End map_filter.


(*

A library for finite sets, implemented as lists

Much of this is taken from Coq std libraries , especially
Coq.List.ListSet

Here use [Context `{eq_dec: EqDecision elt}] instead of, in
  Coq.List.ListSet, [Hypothesis Aeq_dec : forall x y:A, {x = y} + {x
  <> y}]

Here we uniformly change prefix [set_] into [s_] to avoid name
conflict with Coq.List.ListSet.

- We never rely on a NoDup precondition about inputs.  Thus we do not
  promise no-dup as a postcondition.  NoDup-ness should be considered
  a best-effort property here.

[nodup] is the function removing duplicates, [NoDup] is the predicate
asserting no duplicates

 *)

  

Section first_definitions.

  Variable elt : Type.
  Context  `{EqDec: EqDecision elt}.
  (* Context  `{eq_dec: EqDecision elt}. *)

  Notation set := (list elt).

  Definition elements {s : set} : (list elt) := s.

  (* Definition setify : list elt -> list elt  := nodup eq_dec. *)

  (** have to bridge between EqDecision and stdlib sumbool *)

  Definition empty_set : set := nil.
  Definition is_empty (l : set) : Prop := l = empty_set.
  
  Definition subset (s s' : set) : Prop := incl s s' .
  Definition set_equal (s s' : set) : Prop := (subset s s') /\ (subset s' s).


  (** Two equivalent definitions *)
  Definition  strict_subset (s1 s2 : set) :=
    s1 <<= s2 /\ ~ s2 <<= s1.

  Definition subset_not_equal (s s' : set) : Prop := 
    subset s s' /\ s =/= s'.

  Lemma not_subset s1 s2 :
    ~ s2 <<= s1 ->
    exists (x: elt), In x s2 /\ ~  In x s1.
  Proof.
    intros H.
    unfold incl in H.
    (* set (p:= (fun x => ~ In x s1)). *)
    assert (h:= @list_exists elt s2 ).
    apply h.
    - intros. now apply list_in_dec.
    - easy.
  Qed.

  Lemma subset_not s1 s2 :
    (exists (x: elt), In x s2 /\ ~  In x s1) ->
    ~ s2 <<= s1 .
  Proof using Type.
    intros H.
    unfold incl.
    intros HF.
    destruct H as [x H].
    firstorder.
  Qed.


  Lemma strict_not_equal (s1 s2: set) :
    strict_subset s1 s2 ->
    subset_not_equal s1 s2.
  Proof using Type.
    intros H; destruct H as [H1 H2].
    split.
    - easy.
    - intros HF;  unfold set_equal in HF;
        unfold incl in *; unfold equi in HF;
        tauto.
  Qed.

  Lemma not_equal_strict (s1 s2: set) :
    subset_not_equal s1 s2 ->
    strict_subset s1 s2 .
  Proof using Type.
    intros H; destruct H as [H1 H2].
    split.
    - easy.
    - intros HF;  unfold set_equal in H2; 
        unfold incl in * ; unfold equi in H2;
        tauto.
  Qed.

  Lemma strict_subset_witness s1 s2 :
    strict_subset s1 s2 ->
    exists (x: elt), In x s2 /\ ~  In x s1.
  Proof.
    unfold strict_subset.   intros. now apply not_subset.
  Qed.

  Lemma card_strict_subset s1 s2 :
    strict_subset s1 s2 -> card s1 < card s2.
  Proof using Type.
    intros H.
    unfold strict_subset in H.
    destruct H as [H1  H2].
    apply not_subset in H2.
    destruct H2 as [x [H21 H22]].
    eapply card_lt .
    - apply H1.
    - eassumption.
    - assumption.
  Qed.

Lemma subset_refl (x: set) :
  subset x x.
Proof.
  intros H; auto.
Qed.

Lemma subset_trans (x y z : set) : 
  subset x y ->
  subset y z ->
 subset x z.
Proof.
  unfold subset in *.
  unfold incl in *.
  intros H1 H2 a H3.
  specialize (H1 a).
  specialize (H2 a).
  tauto.
Qed.


Lemma subset_app_introR (x y : set) : 
  subset x (x++y) .
Proof.
  intros e H.
  apply in_or_app; now left.
Qed.

Lemma subset_app_introL (x y : set) : 
  subset y (x++y) .
Proof.
  intros e H.
  apply in_or_app; now right.
Qed.


Lemma subset_app_elim (x y z : set) : 
  subset (x++y) z ->
  subset x z 
  /\ subset y z.
Proof.
  intros H.
  unfold subset in *.
  unfold incl in *.
  split.
  - intros.
    apply H.
    apply in_or_app. now left.
  - intros. apply H.
    apply in_or_app. now right.
Qed.


Lemma subset_in (e: elt) (s : set) :
  subset [e] s ->
  In e s.
Proof.
  intros H.
  apply (H e).
  simpl; now left.
Qed.

  Definition choose (s : set) : option elt :=
    match s with
    | nil => None
    | x::_ => Some x
    end.

(** Adds to the end ... *)
  Fixpoint set_add (a:elt) (x:set) : set :=
    match x with
    | nil => a :: nil
    | a1 :: x1 =>
        match eq_dec a a1 with
        | left _ => a1 :: x1
        | right _ => a1 :: set_add a x1
        end
    end.

  Fixpoint set_mem (a:elt) (x:set) : bool :=
    match x with
    | nil => false
    | a1 :: x1 =>
        match eq_dec a a1 with
        | left _ => true
        | right _ => set_mem a x1
        end
    end.


(** Is [x] not in list [l]? *)

Definition not_in (x: elt) (l: list elt): bool :=
  negb (set_mem x l).


(** Does list [l] contain duplicates? *)
Fixpoint has_no_dups (l: list elt): bool :=
  match l with
  | nil => true
  | x :: xs => not_in x xs && has_no_dups xs
  end.


  (** If [a] belongs to [x], removes [a] from [x]. If not, does
  nothing.  We don't rely on the precondition that the inputs are
  no-dup: we remove all occurrences.  *)

  Fixpoint set_remove (a:elt) (x:set) : set :=
    match x with
    | nil => empty_set
    | a1 :: x1 =>
        match eq_dec a a1 with
        | left _ => set_remove a x1
        | right _ => a1 :: set_remove a x1
        end
    end.

  Fixpoint set_inter (x:set) : set -> set :=
    match x with
    | nil => fun y => nil
    | a1 :: x1 =>
        fun y =>
          if set_mem a1 y then a1 :: set_inter x1 y else set_inter x1 y
    end.

  Fixpoint set_union (x y:set) : set :=
    match y with
    | nil => x
    | a1 :: y1 => set_add a1 (set_union x y1)
    end.

  Notation "A +++ B" := (set_union A B) (at level 70).

  (** returns the set of all els of [x] that does not belong to [y] *)
  Fixpoint set_diff (x y:set) : set :=
    match x with
    | nil => nil
    | a1 :: x1 =>
        if set_mem a1 y then set_diff x1 y else set_add a1 (set_diff x1 y)
    end.

  Fixpoint set_partition (f : elt -> bool) (s : set) : set * set :=
    match s with
    | nil => (nil, nil)
    | x :: l =>
        let (s1, s2) := set_partition f l in
        if f x then ((set_add x s1) , s2) else (s1, (set_add x s2))
    end.


  (* Definition set_In : elt -> set -> Prop := In (A:=elt). *)

  (* ============ THERE ================= *)
  
  (* Two induction principles for finite sets *)
  Lemma set_mem_ind :
    forall (B:Type) (P:B -> Prop) (y z:B) (a:elt) (x:set),
      (In a x -> P y) -> P z -> P (if set_mem a x then y else z).
  Proof using Type.
    simple induction x; simpl; intros.
    assumption.
    elim (eq_dec a a0); auto with datatypes.
  Qed.

  Lemma set_mem_ind2 :
    forall (B:Type) (P:B -> Prop) (y z:B) (a:elt) (x:set),
      (In a x -> P y) ->
      (~ In a x -> P z) -> P (if set_mem a x then y else z).
  Proof using Type.
    simple induction x; simpl.
    - intros H0 H1. apply H1; red; trivial.
    - intros a0 l H0 H1 H2. 
      case (eq_dec a a0); auto with datatypes.
      intro Hneg; apply H0; intros; auto.
      apply H2; red; intro H3.
      case H3; auto.
  Qed.

  Lemma set_mem_correct1 :
    forall (a:elt) (x:set), set_mem a x = true -> In a x.
  Proof using Type.
    simple induction x; simpl.
    discriminate.
    intros a0 l; elim (eq_dec a a0); auto with datatypes.
  Qed.

  Lemma set_mem_correct2 :
    forall (a:elt) (x:set), In a x -> set_mem a x = true.
  Proof using Type.
    simple induction x; simpl.
    intro Ha; elim Ha.
    intros a0 l; elim (eq_dec a a0); auto with datatypes.
    intros H1 H2 [H3| H4].
    absurd (a0 = a); auto with datatypes.
    auto with datatypes.
  Qed.

  Lemma set_mem_complete1 :
    forall (a:elt) (x:set), set_mem a x = false -> ~ In a x.
  Proof using Type.
    simple induction x; simpl.
    tauto.
    intros a0 l; elim (eq_dec a a0).
    intros _ _ [=].
    unfold not; intros H H0 H1 [ | ]; auto with datatypes.
  Qed.

  Lemma set_mem_complete2 :
    forall (a:elt) (x:set), ~ In a x -> set_mem a x = false.
  Proof using Type.
    simple induction x; simpl.
    tauto.
    intros a0 l; elim (eq_dec a a0).
    intros H H0 []; auto with datatypes.
    tauto.
  Qed.


(* #[local] Hint Unfold eq_dec_refl : core. *)

  Lemma set_add_intro1 :
    forall (a b:elt) (x:set), In a x -> In a (set_add b x).
 
  Proof.
    induction x; simpl.
    - auto. 
    - intros [H1 | H2].
      + subst.
      destruct (eq_dec b a).
      -- auto.
      -- auto.
      + destruct (decide (b=a0)); subst.
        ++ rewrite eq_dec_refl.
           specialize (IHx H2).
           auto.
        ++ rewrite neq_eq_dec.
           specialize (IHx H2).           
           auto.
           easy.
  Qed. 

  Lemma set_add_intro2 :
    forall (a b:elt) (x:set), a = b -> In a (set_add b x).

  Proof using Type.
    unfold In; simple induction x; simpl.
    auto with datatypes.
    intros a0 l H Hab.
    - destruct (decide (b=a0)); subst.
      + specialize (H eq_refl).  rewrite eq_eq_dec. now auto.
        easy.
      + specialize (H eq_refl); auto.
        rewrite neq_eq_dec.
        right.
        now auto.
        easy.
Qed.

  #[local]
    Hint Resolve set_add_intro1 set_add_intro2 : core.

  Lemma set_add_intro :
    forall (a b:elt) (x:set), a = b \/ In a x -> In a (set_add b x).

  Proof using Type.
    intros a b x [H1| H2]; auto with datatypes.
  Qed.

  Lemma set_add_elim :
    forall (a b:elt) (x:set), In a (set_add b x) -> a = b \/ In a x.

  Proof using Type.
    unfold In.
    simple induction x.
    simpl; intros [H1| H2]; auto with datatypes.
    simpl; do 3 intro.
    elim (eq_dec b a0).
    simpl; tauto.
    simpl; intros H0 [ | ].
    trivial with datatypes.
    tauto.
    tauto.
  Qed.

  Lemma set_add_elim2 :
    forall (a b:elt) (x:set), In a (set_add b x) -> a <> b -> In a x.
  Proof using Type.
    intros a b x H H0.
    case (@set_add_elim a b x  H); intros; trivial.
    congruence.
  Qed.


  Lemma set_add_not_empty : forall (a:elt) (x:set), set_add a x <> empty_set.
  Proof using Type.
    simple induction x; simpl.
    discriminate.
    intros; elim (eq_dec a a0); intros; discriminate.
  Qed.

  Lemma set_add_iff a b l : In a (set_add b l) <-> a = b \/ In a l.
  Proof using Type.
    split. apply set_add_elim. apply set_add_intro.
  Qed.

  Lemma incl_add a w :
    w <<= set_add a w.
  Proof.
    intros x H.
    apply set_add_intro.
    now right.
Qed.


  Lemma set_add_nodup a l : NoDup l -> NoDup (set_add a l).
  Proof using Type.
    induction 1 as [ |x l H H' IH]; simpl.
    - constructor; [ tauto | constructor ].
    - destruct (eq_dec a x) as [<-|Hax]; constructor; trivial.
      rewrite set_add_iff.
      firstorder.
  Qed.

  (** *** remove lemmas *)
  Lemma set_remove_1 (a b : elt) (l : set) :
    In a (set_remove b l) -> In a l.
  Proof using Type.
    induction l as [ |x xs Hrec].
    - intros. auto.
    - simpl. destruct (eq_dec b x).
      * tauto.
      * intro H. destruct H.
      + rewrite H. apply in_eq.
      + apply in_cons. apply Hrec. assumption.
  Qed.

  Lemma set_remove_2 (a b:elt) (l : set) :
    NoDup l -> In a (set_remove b l) -> a <> b.
  Proof using Type.
    induction l as [ |x l IH]; intro ND; simpl.
    - tauto.
    - inversion_clear ND.
      destruct (eq_dec b x) as [<-|Hbx]. 
      + intros. now apply IH.
      + destruct 1; subst; auto.
  Qed.

  Lemma set_remove_3 (a b : elt) (l : set) :
    In a l -> a <> b -> In a (set_remove b l).
  Proof using Type.
    induction l as [ |x xs Hrec].
    - now simpl.
    - simpl. destruct (eq_dec b x) as [<-|Hbx]; simpl; firstorder;
      congruence.
  Qed.

  Lemma set_remove_iff (a b : elt) (l : set) :
    NoDup l -> (In a (set_remove b l) <-> In a l /\ a <> b).
  Proof using Type.
    split; try split.
    - eapply set_remove_1; eauto.
    - eapply set_remove_2; eauto.
    - destruct 1; apply set_remove_3; auto.
  Qed.

  Lemma set_remove_nodup a l : NoDup l -> NoDup (set_remove a l).
  Proof using Type.
    induction 1 as [ |x l H H' IH]; simpl.
    - constructor.
    - destruct (eq_dec a x) as [<-|Hax]; trivial.
      constructor; trivial.
      rewrite set_remove_iff; trivial. firstorder.
  Qed.

  (** *** union lemmas *)
  Lemma set_union_intro1 :
    forall (a:elt) (x y:set), In a x -> In a (set_union x y).
  Proof using Type.
    simple induction y; simpl; auto with datatypes.
  Qed.

  Lemma set_union_intro2 :
    forall (a:elt) (x y:set), In a y -> In a (set_union x y).
  Proof using Type.
    simple induction y; simpl.
    tauto.
    intros; elim H0; auto with datatypes.
  Qed.

  #[local]
    Hint Resolve set_union_intro2 set_union_intro1 : core.

  Lemma set_union_intro :
    forall (a:elt) (x y:set),
      In a x \/ In a y -> In a (set_union x y).
  Proof using Type.
    intros; elim H; auto with datatypes.
  Qed.

  Lemma set_union_elim :
    forall (a:elt) (x y:set),
      In a (set_union x y) -> In a x \/ In a y.
  Proof using Type.
    simple induction y; simpl.
    auto with datatypes.
    intros. 
    generalize (set_add_elim H0).
    intros [H1| H1].
    auto with datatypes.
    tauto.
  Qed.

  Lemma set_union_iff a l l': In a (set_union l l') <-> In a l \/ In a l'.
  Proof using Type.
    split. apply set_union_elim. apply set_union_intro.
  Qed.

  Lemma set_union_nodup l l' : NoDup l -> NoDup l' -> NoDup (set_union l l').
  Proof using Type.
    induction 2 as [ |x' l' ? ? IH]; simpl; trivial. now apply set_add_nodup.
  Qed.

  Lemma set_union_emptyL :
    forall (a:elt) (x:set), In a (set_union empty_set x) -> In a x.
    intros a x H; case (@set_union_elim  _ _ _ H); auto || contradiction.
    (* intros a x H; case (set_union_elim _ _ _ H); auto || contradiction. *)
  Qed.

  Lemma set_union_emptyR :
    forall (a:elt) (x:set), In a (set_union x empty_set) -> In a x.
    intros a x H; case (set_union_elim H); auto || contradiction.
    (* intros a x H; case (set_union_elim _ _ _ H); auto || contradiction. *)
  Qed.

  Lemma union_incl_left (s t: set):
    s <<=  (set_union s t).
  Proof using Type.
    unfold incl;
      intros; now apply set_union_intro1.
  Qed.

  Lemma union_incl_right (s t : set) :
    s <<=  (set_union t s).
  Proof using Type.
    unfold incl.
    intros. auto.
    (* intros; now apply set_union_intro2. *)
  Qed.


  (** *** intersection lemmas *)
  Lemma set_inter_intro :
    forall (a:elt) (x y:set),
      In a x -> In a y -> In a (set_inter x y).
  Proof using Type.
    simple induction x.
    auto with datatypes.
    simpl; intros a0 l Hrec y [Ha0a| Hal] Hy.
    simpl; rewrite Ha0a.
    (* generalize (set_mem_correct1 ). *)
    generalize (@set_mem_complete1 a y).
    elim (set_mem a y); simpl; intros.
    auto with datatypes.
    absurd (In a y); auto with datatypes.
    elim (set_mem a0 y); [ right; auto with datatypes | auto with datatypes ].
  Qed.

  Lemma set_inter_elim1 :
    forall (a:elt) (x y:set), In a (set_inter x y) -> In a x.
  Proof using Type.
    simple induction x.
    auto with datatypes.
    simpl; intros a0 l Hrec y.
    generalize (@set_mem_correct1 a0 y).
    (* generalize (set_mem_correct1 a0 y). *)
    elim (set_mem a0 y); simpl; intros.
    elim H0; eauto with datatypes.
    eauto with datatypes.
  Qed.

  Lemma set_inter_elim2 :
    forall (a:elt) (x y:set), In a (set_inter x y) -> In a y.
  Proof using Type.
    simple induction x.
    simpl; tauto.
    simpl; intros a0 l Hrec y.
    generalize (@set_mem_correct1 a0 y).
    (* generalize (set_mem_correct1 a0 y). *)
    elim (set_mem a0 y); simpl; intros.
    elim H0;
      [ intro Hr; rewrite <- Hr; eauto with datatypes | eauto with datatypes ].
    eauto with datatypes.
  Qed.

  #[local]
    Hint Resolve set_inter_elim1 set_inter_elim2 : core.

  Lemma set_inter_elim :
    forall (a:elt) (x y:set),
      In a (set_inter x y) -> In a x /\ In a y.
  Proof using Type.
    eauto with datatypes.
  Qed.

  Lemma set_inter_iff a l l' : In a (set_inter l l') <-> In a l /\ In a l'.
  Proof using Type.
    split.
    - apply set_inter_elim.
    - destruct 1. now apply set_inter_intro.
  Qed.

  Lemma set_inter_nodup l l' : NoDup l -> NoDup l' -> NoDup (set_inter l l').
  Proof using Type.
    induction 1 as [ |x l H H' IH]; intro Hl'; simpl.
    - constructor.
    - destruct (set_mem x l'); auto.
      constructor; auto. rewrite set_inter_iff; tauto.
  Qed.

  Lemma set_diff_intro :
    forall (a:elt) (x y:set),
      In a x -> ~ In a y -> In a (set_diff x y).
  Proof using Type.
    simple induction x.
    simpl; tauto.
    simpl; intros a0 l Hrec y [Ha0a| Hal] Hay.
    rewrite Ha0a; generalize (@set_mem_complete2 _ _ Hay).
    elim (set_mem a y);
      [ intro Habs; discriminate Habs | auto with datatypes ].
    elim (set_mem a0 y); auto with datatypes.
  Qed.

  Lemma set_diff_elim1 :
    forall (a:elt) (x y:set), In a (set_diff x y) -> In a x.
  Proof using Type.
    simple induction x.
    simpl; tauto.
    simpl; intros a0 l Hrec y; elim (set_mem a0 y).
    eauto with datatypes.
    intro; generalize (@set_add_elim _ _ _ H).
    intros [H1| H2]; eauto with datatypes.
  Qed.

  Lemma set_diff_elim2 :
    forall (a:elt) (x y:set), In a (set_diff x y) -> ~ In a y.
    intros a x y; elim x; simpl.
    intros; contradiction.
    intros a0 l Hrec.
    apply set_mem_ind2; auto.
    intros H1 H2; case (@set_add_elim _ _ _ H2); intros; auto.
    rewrite H; trivial.
  Qed.

  Lemma set_diff_elim :
    forall (a:elt) (x y:set), In a (set_diff x y) -> 
                              In a x /\ ~ In a y.
  Proof using Type.
    intros.
    split.
    - now apply set_diff_elim1 with y.
    - now apply set_diff_elim2 with x.
  Qed.

  Lemma set_diff_iff a l l' : In a (set_diff l l') <-> In a l /\ ~In a l'.
  Proof using Type.
    split.
    - split; [eapply set_diff_elim1 | eapply set_diff_elim2]; eauto.
    - destruct 1. now apply set_diff_intro.
  Qed.

  Lemma set_diff_nodup l l' : NoDup l -> NoDup l' -> NoDup (set_diff l l').
  Proof using Type.
    induction 1 as [ |x l H H' IH]; intro Hl'; simpl.
    - constructor.
    - destruct (set_mem x l'); auto using set_add_nodup.
  Qed.

  Lemma set_diff_trivial : forall (a:elt) (x:set), ~ In a (set_diff x x).
    red; intros a x H.
    apply (@set_diff_elim2 _ _ _ H).
    apply (@set_diff_elim1 _ _ _ H).
  Qed.

  Lemma diff_empty (l : set):  set_equal (set_diff l empty_set) l.
  Proof using Type.
    unfold set_equal.
    split.
    - unfold subset. unfold incl. intros.
      now apply set_diff_elim1 with empty_set.
    - unfold subset. unfold incl. intros.
      apply set_diff_iff.
      split; easy.
  Qed.

  (** a grab-bag... *)

  Lemma diff_contra u1 u2 s1 s2 :
    u2 <<= u1 ->
    s1 <<= s2 ->
    (set_diff u2 s2) <<= (set_diff u1 s1).
  Proof using Type.
    intros H1 H2u x H.
    apply set_diff_elim in H. destruct H.
    apply set_diff_intro;
      unfold incl in *; firstorder.
  Qed.

  

  Lemma diff_strict u s1 s2 :
    strict_subset s1 s2 ->
    s2 <<= u ->
    strict_subset (set_diff u s2) (set_diff u s1).
  Proof using Type.
    unfold strict_subset.
    intros H1 H2. 
    destruct H1 as [x H12].
    split.
    - now apply diff_contra.
    - apply subset_not.
      apply not_subset in H12.
      destruct H12 as [x2 [P1 P2]].
      exists x2.
      split.
      + apply set_diff_intro.
        -- now apply (H2 x2).
        -- easy.
      + intros HF.
        now apply set_diff_elim2 in HF.
  Qed.



  Lemma diff_contra' u s1 s2 :
    s1 <<= s2 ->
    s2 <<= u ->
    (set_diff u s2) <<= (set_diff u s1).
  Proof using Type.
    intros H1 H2u x H.
    apply set_diff_intro.
    - now apply set_diff_elim1 in H.

    - apply set_diff_elim2 in H.
      apply incl_not with s2; auto.
  Qed.

  Lemma diff_smaller u s1 s2 :
    strict_subset s1 s2 ->
    s2 <<= u ->
    card  (set_diff u s2) < card (set_diff u s1).
  Proof using Type.
    intros;
      apply card_strict_subset;
      now apply diff_strict.
  Qed.


End first_definitions.




  #[export]
    Hint Resolve 
    (* one of these causes an eauto stack oveflow *)
    (* set_add_intro set_add_elim set_add_elim2  *)
    incl_add
    set_diff_intro set_diff_trivial 
    diff_contra card_strict_subset 
    diff_strict diff_smaller
  : core.








  (* ================================================ *)
  (* ================================================ *)
  (* ================================================ *)

Section DiffDecrease.

(** Condition for a set-difference to get strictly smaller.
    
    Used, eg, in the Saturation development
*)
Variable X: Type.
Context  `{eq_dec: EqDecision X}.
  
Variable u ys ys' : set X.

Hypothesis ys'ys : ys' <<= ys.
Hypothesis somex :
  exists x, In x u /\ In x ys /\ ~ In x ys'.

Lemma strict_subset_diff :
  strict_subset (set_diff u ys) (set_diff u ys').
Proof using somex ys'ys.
  unfold strict_subset.
  split.
  apply diff_contra.  
  - easy.
  - easy.
  - destruct somex as [x P].
    destruct P as [p1 [p2 p3]].
    intros HF.
    unfold incl in HF.
    specialize (HF x).
    assert (a: In x (set_diff u ys')).
    { apply set_diff_intro; easy. }
    specialize (HF a).
    apply set_diff_elim in HF. destruct HF. 
    congruence.
Qed.

End DiffDecrease.

Arguments empty_set {elt}%type_scope.

Section OtherDefinitions.

  Definition set_prod : forall {A B:Type}, set A -> set B -> set (A * B) :=
    list_prod.

  (** [B^A], set of applications from [A] to [B] *)
  Definition set_power : forall {A B:Type}, set A -> set B -> set (set (A * B)) :=
    list_power.

  Definition set_fold_left {A B:Type} : (B -> A -> B) -> set A -> B -> B :=
    fold_left (A:=B) (B:=A).

  Definition set_fold_right {A B:Type} (f:A -> B -> B) (x:set A)
    (b:B) : B := fold_right f b x.

  Definition set_map {A B:Type} 
    {Bdec: EqDecision B}
    (f : A -> B) (x : set A) : set B :=
    set_fold_right (fun a => set_add  (f a)) x (empty_set).


End OtherDefinitions.


#[export] Instance diff_proper X `{eq_dec: EqDecision X} : 
  Proper (@equi X ==> @equi X ==> @equi X) (@set_diff X eq_dec).
Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  (* destruct D, E; auto. *)
  split.
  - intros a P.
    apply set_diff_elim in P. destruct P.
    apply set_diff_intro.
    + now rewrite <- D.
    + now rewrite <- E.
  - intros a P.
    apply set_diff_elim in P.
    apply set_diff_intro.
    + now rewrite D .
    + now rewrite E.
Defined.

#[export] Instance incl_dec  {X: Type} { _ : EqDecision X}: 
  forall xs ys, Decision (@incl X  xs ys).
Proof. 
  intros. unfold Decision.
  unfold incl.
  apply list_forall_dec.
  apply _.
Defined.

#[export] Instance equi_dec  {X: Type} { _ : EqDecision X} : 
  forall xs ys, Decision (@equi X xs ys).
Proof.
  intros xs ys. apply _.
Defined.


(** A general combinator:
add elts of [s] to [acc] that are NOT in [guard] *)

Definition guarded_add {X: Type} {EqDec: EqDecision X} (guard s acc : list X) : list X :=
  set_union (set_diff s guard) acc.



(* =============================== *)

(** * Boolean Approach *)

Section BoolList.

  Variable X : Type.

  Context  `{eqb_dec: EqbDec X}.

  (** so have [eqb: X -X -> bool] and
      [eqb_eq : forall x y, if eqb x y then x = y else x <> y]
   *)

  Fixpoint for_allb  {A: Set} (f : A -> bool) (s : set A) : bool :=
    match s with
    | nil => true
    | x :: l => if f x then for_allb f l else false
    end.

  Fixpoint exists_b {A: Set} (f : A -> bool) (s : set A) : bool :=
    match s with
    | nil => false
    | x :: l => if f x then true else exists_b f l
    end.


  Definition MemP {A} s x := @In A x s.

  (* (** Boolean version of In *) *)
  Fixpoint inb (a : X) (ls : list X) : bool :=
    match ls with
    | [] => false
    | b :: m =>  beq b a  || inb a m
    end.

 Definition neg_inb 
   (a: X) (ls: list X) : bool :=
   negb (inb a ls).

  Lemma inb_In  (a : X) (ls : list X) : 
    inb a ls = true -> In a ls.
  Proof using Type.
    intros H. 
    induction ls as [ | x rest IH]; simpl; auto.
    - inv H.
    - destruct (beq_reflect x a).
      + left; auto.
      + right.
        simpl in H.
        rewrite orb_true_iff in H. destruct H as [h1 | h2].
        destruct (beq_reflect x a);
          congruence; auto. auto.
  Qed.

  Lemma In_inb (a : X) (ls : list X) : 
    In a ls -> inb a ls = true.
  Proof using Type.
    intros H. induction ls as [ | x rest IH]; simpl; auto.
    rewrite orb_true_iff. destruct H as [h1 | h2].
    - left.  now destruct (beq_reflect x a).
    - right; auto.
  Qed.


  Lemma inb_reflect (a : X) (ls : list X) : 
    reflect (In a ls) (inb a ls ).
  Proof using Type.
    apply iff_reflect.
    split.
    - apply In_inb.
    - apply inb_In.
  Qed.

Lemma inb_false (a : X) (ls : list X) : 
  negb (inb a ls) = true <-> ~ In a ls.
Proof using Type.
rewrite negb_true_iff.
destruct (inb_reflect a ls).
- split;  intros; congruence.
- tauto.
Qed.

  Definition is_emptyb {X: Type} (eqb: X -> X -> bool) (l: set X)  : bool := 
    match l with [] => true | _ => false end.

  Fixpoint inclb (s s': set X ) : bool := 
    match s with 
    | [] => true
    | x :: rest => (inb  x s') && (inclb rest s')
    end.
        
  Definition equib (s s' : set X) : bool := 
    andb (inclb s s') (inclb s' s).

    Definition nequib  (s s' : set X ) : bool :=
    negb (equib s s').

  Lemma equib_nequib (s s' : set X) :
    nequib s s' = true <->
    equib s s' = false.
  Proof using Type.
    unfold nequib.
    destruct (equib s s') eqn: e;
    simpl; split; congruence.
Qed.
  

(** inclb refelcts incl *)
Lemma incl_inclb (s s' : set X ) :
  incl s s' -> inclb s s' = true.
Proof using Type.
  intros.
  induction s as [ | x rest IH]; simpl; auto.
  apply incl_lcons in H. destruct H.
  apply andb_true_intro. split.
  + now apply In_inb.
  + auto.
Qed.

Lemma inclb_incl  (s s' : set X) :
  inclb  s s' = true ->   incl s s'.
Proof using Type.
  intros H.
  induction s as [ | x rest IH]; simpl; auto.  
  apply incl_lcons. split.
  - simpl in H.
    apply inb_In. 
    apply andb_true_iff in H.
    tauto.
  - apply IH.
    simpl in H.
    apply andb_true_iff in H.
    tauto.
Qed.

Lemma equi_equib (s s' : set X) :
  equi s s' -> equib  s s' = true.
Proof using Type.
  intros H.
  destruct H as [h1 h2].
  apply andb_true_iff.  split; now apply incl_inclb.
Qed.

Lemma equib_equi (s s' : set X) :
equib   s s' = true -> equi s s'.
Proof using Type.
  intros H.
  unfold equib in H.
  apply andb_true_iff in H. destruct H as [h1 h2].
  split;
  now apply inclb_incl.
Qed.

End BoolList.

(* =================================== *)
Section Sort.

  Variables (A : Type) (cmp : A -> A -> comparison).

  Fixpoint insert x (l : list A) :=
    match l with
      | nil => cons x nil
      | cons y m =>
        match cmp x y with
          | Gt => cons y (insert x m)
          | _ => cons x l
        end
    end.

  Fixpoint sort (l : list A) : list A :=
    match l with
      | nil => nil
      | cons x m => insert x (sort m)
    end.

End Sort.

(** returns 0 on nil ..*)
Fixpoint list_max (ls : list nat) : nat :=
    match ls with 
      [] => 0
    | n:: rest =>
        max n (list_max rest)
end.

(** returns 0 on nil ..*)
Fixpoint list_sum (ls : list nat) : nat :=
    match ls with 
      [] => 0
    | n:: rest =>
         n + (list_sum rest)
end.
              

Fixpoint list_min
  (ls: list nat) : option nat :=
  match ls with 
    [] => None
  | n::rest => match list_min rest with
                 None => Some n
               | Some m => Some (min n m)
               end
  end.

(* Squaring a list, ie the set of pairs (x,y) where x and y are from
the original list *)
Definition lsquare {X:Type} (ls: list X) : list (X * X) :=
  list_prod ls ls.

(* Enrich a list with indices *)
Fixpoint indexed_hlp 
   (start: nat) {X: Type} (xs : list X) : list (nat * X) :=
  match xs with 
    [] => []
  | x::rest => (start , x) :: (indexed_hlp (1+start) rest)
end.

Definition indexed 
  {X: Type} (xs : list X) : list (nat * X) :=
  indexed_hlp 0 xs.


(** accumulating variation on [fold_left]
*)

(** Apply [do_one] to each member of [bs] but accumulating the initial
parameter as we go.

If in base case we did [] => [i] we get a result one longer than [bs];
startin with init value

 *)
Fixpoint map_accum
  {A B : Type} 
  (do_one : A -> B -> A)
  (i: A) (bs : list B) :
  list A :=
  match bs with
    [] => []
  | ev::rest =>
      (do_one i ev) :: map_accum do_one (do_one i ev) rest
  end. 


(* ----------------------- *)

(* Apply [do_one] to each member of [bs] ; accumulating the initial
parameter as we go.  But fail if any [do_one] calls fail *)

Fixpoint map_accum_opt
  {A B : Type} 
  (do_one_opt : A -> B -> option A)
  (i: A) (bs : list B) :
  option (list A) :=
  match bs with
    [] => Some []
  | ev::rest =>
      letM answer_head := do_one_opt i ev in
      letM answer := map_accum_opt do_one_opt answer_head rest in
        Some (answer_head :: answer )
  end  .

Fixpoint map_accum_opt'
  {A B : Type} 
  (do_one_opt : A -> B -> option A)
  (i: A) (bs : list B) :
  option (list A) :=
  match bs with
    [] => Some []
  | ev::rest =>
      match do_one_opt i ev with
        None => None 
      | Some answer_head =>
      match map_accum_opt' do_one_opt answer_head rest  with
        None => None
      | Some answer =>
          Some (answer_head :: answer )
  end end end.

(* ================================ *)
(** Things NOT already in std library ListSet *)

Section Extra_ListSet.

  Variable elt : Type.
  Context  `{EqDec: EqDecision elt}.
  (* Context  `{eq_dec: EqDecision elt}. *)

  Notation set := (list elt).


Lemma add_iff (a: elt) (s : set) :
  forall x, In x (set_add a s) <->
              x=a \/ In x s.
Proof.
  intros x.
  split.
  - intros H.
    assert (h:= @set_add_elim2 elt EqDec x a s H). 
    tauto.
  - intros H.
    now apply set_add_intro.
Qed.

End Extra_ListSet.

#[export] Hint Resolve subset_app_elim : core.

Lemma forallb_nil {A: Type} (f: A -> bool) :
  forallb f [] = true.
Proof.
easy.
Qed.


Lemma Forall_app_singleton
  {A: Type} (P: A -> Prop)
  (ls: list A) (a: A) :
  Forall P ls ->
  P a ->
  Forall P (ls ++ [a]).
Proof.  
  intros Hls Ha.
  apply (Forall_app P); split.
  - easy.
  - apply (@Forall_cons A P a [] Ha). 
    apply Forall_nil.
Qed.

(* ??????????????????? *)

(* ----------------------------------------- *)
(** *** mapping a relation over a list *)

(** list of X is pointwise r-related to list of Y.
 The lists must be of the same length.
*)

Inductive List_mapR
  {X Y : Type} (r: rel X Y) : (rel (list X) (list Y)) :=
| List_mapRnil: List_mapR r [] []
                      
| List_mapRcons x y xs ys :
  r x y ->
  List_mapR r xs ys ->
  List_mapR r (x::xs) (y::ys).


(** [List_mapR] is decidable when [r] is *)
#[export] Instance List_mapR_dec {X Y : Type} (r: X -> Y -> Prop)
  (* (r_eq_dec: forall x y, Decision (r x y)) :  *)
  `{forall x y, Decision (r x y)} :
    forall xs ys, Decision (List_mapR r xs ys).
Proof.
  intros xs.
  induction xs as [| x restx IH].
  - destruct ys as [| y resty] eqn:eys .
    + left; constructor.
    + right. intros F; inv F.

  - intros ys.
    destruct ys as [| y resty] eqn:eys .
    + right. intros F; inv F.
    + destruct (decide (r x y)) eqn:er.
      -- specialize (IH resty).
         destruct IH eqn:eIH.
         ++ left. constructor; easy.
         ++ right; intros F; inv F; easy.
      -- right; intros F; inv F; easy.
Defined.

Fixpoint List_mapRb
  {X Y : Type} (r: relb X Y) (xs: list X)(ys: list Y) : bool :=
  match xs, ys with
    [] , [] => true
  | (x::xs) ,  (y::ys) => r x y &&
                            List_mapRb r xs ys
  | _ , _ => false
end.

Lemma List_mapR_List_mapRb {X Y: Type}
  (r : rel X Y) (rb : relb X Y) (xs: list X)(ys: list Y) :
  (forall x y, r x y -> rb x y = true) ->
  List_mapR r xs ys ->
  List_mapRb rb xs ys = true.
Proof.
  intros H1 H2.
  generalize dependent ys.
  induction xs as [| x rest IH].
  - intros.  inv H2; easy.
  - intros. cbn.
    destruct ys as [| rest'].
    + inv H2.
    + inv H2. 
      apply andb_true_intro.
      split.
      specialize (H1 x rest'); auto.
      now apply IH.
Qed.

Lemma List_mapRb_List_mapR {X Y: Type}
  (r : rel X Y) (rb : relb X Y) (xs: list X)(ys: list Y) :
  (forall x y, rb x y = true -> r x y) ->
  List_mapRb rb xs ys = true ->
  List_mapR r xs ys.
Proof.
  intros.
  generalize dependent ys.
  induction xs as [| x restxs IH].
  - intros ys H1. 
    destruct ys as [| y0 restys]; simpl; auto. constructor.
    inv H1.
  - intros ys H1.
    destruct ys as [| y0 restys];  simpl; auto. 
    inv H1; destruct H1 as [H11 H12].
    crush.
    constructor.
    + apply andb_prop in H1;
      apply H; easy.
    + apply IH.
      apply andb_prop in H1; destruct H1 as [H11 H12]; easy.
Qed.

Proposition List_mapR_reflect 
 {X Y: Type} (r : rel X Y) (rb : relb X Y) 
 (xs: list X)(ys: list Y) : 
  (forall x y, r x y <-> rb x y = true) -> 
  reflect (List_mapR r xs ys) (List_mapRb rb xs ys).
Proof.
  intros.
  apply iff_reflect.
  split.
  apply List_mapR_List_mapRb. apply H.
  apply List_mapRb_List_mapR; apply H.
Qed.


Lemma List_mapR_mono
  {X Y : Type} (r r': rel X Y) xs ys :
  (forall x y, (r x y -> r' x y)) ->
  List_mapR r xs ys ->
  List_mapR r'  xs ys .
Proof.
  intros H0 H1.
  induction H1 .
  - constructor.
  - apply H0 in H.
    constructor; easy. 
Qed.

Lemma List_mapR_iff
  {X Y : Type} (r r': rel X Y) xs ys :
  (forall x y, (r x y <-> r' x y)) ->
  List_mapR r xs ys <->
  List_mapR r'  xs ys .
Proof.
  intros .
  split.
  - apply List_mapR_mono.
    apply H.
   - apply List_mapR_mono.
    apply H.
Qed.


(*  Similarly to Act_mapR
 We want this to be an equality, because we want to rewrite
with it.  Seem to have to detour through logical equivalence and
PropExtensionality.  *)


Lemma List_mapR_equiv
  {X Y : Type} (r r': rel X Y) :
  (forall x y, (r x y <-> r' x y)) ->
  List_mapR r  =
  List_mapR r' .
Proof.
  intros .
apply functional_extensionality; intros e. 
apply functional_extensionality; intros d. 
apply propositional_extensionality.
apply List_mapR_iff. easy.
Qed.

(** 
If beta and gamma preserve r then their composition does
*)
Theorem List_mapR_compose
  {T E R : Type}
  (te : T -> E -> Prop)
  (er : E -> R -> Prop):
  forall  (ts : list T) (es : list E)  (rs : list R)
  (ts_te_es : List_mapR te ts es)
  (es_er_rs : List_mapR er es rs),
  List_mapR (composeR te er) ts rs.
Proof.
  intros ts.
  induction ts as [| t rest IH].
  - intros; inv ts_te_es; inv es_er_rs; auto.
    constructor.

  - intros.
    inv ts_te_es.
    inv es_er_rs.
    constructor.
    + exists y; easy.
    + apply IH with ys; easy.
Qed.



(* ========================================= *)

(** Different approaches *)

(* non-inductive direct defn.
Note that the use of opt_mapR  entails that the lists are of the same length.
 *)
Definition List_mapR'
  {X Y :  Type} 
  (r: X -> Y -> Prop) 
  (xs: list X) (ys: list Y) : Prop :=
  forall n,
    (opt_mapR r (nth_error xs n)  (nth_error ys n) ).

(** List_mapR less than m.   

m=0 is vacuously true (since nth starts counting at 0)
*)
Definition List_mapR_n (m: nat)
  {X Y :  Type} 
  (r: X -> Y -> Prop) 
  (xs: list X) (ys: list Y) : Prop :=
  forall n,
    n < m  ->
    (opt_mapR r (nth_error xs n)  (nth_error ys n) ).

(* the E-list can be smaller; we only r-related the 
initial segment of the T-list)
*) 
Inductive  List_mapR_neq
  {T E :  Type} 
  (r: T -> E -> Prop) 
  : list T -> list E -> Prop :=
| pwr_neq_nil ts :  List_mapR_neq r ts []
                              
| pwr_neq_cons t ts e es :
  r t e ->
  List_mapR_neq r ts es ->
  List_mapR_neq r (t::ts) (e::es)
.

(** Any List_mapR is stable under appending r-related items.
*)
Lemma List_mapR_snoc
  {T E :  Type} 
  (r: T -> E -> Prop) :
  forall   (ts: list T) (es: list E)
  (R : List_mapR r ts es) ,
  forall (t: T) (e: E),
  r t e ->
  List_mapR r (ts++[t]) (es++[e]).
Proof.
  intros ts.
  induction ts as [ | h ts IH].
  - intros es H t e Hr.
    inv H. simpl.
    constructor; easy.

  - intros es H t e Hr.
    inv H. subst.
    specialize (IH ys H4 t e Hr).
    repeat rewrite <- app_comm_cons.
    constructor; easy. 
Qed.


(* 2023 Fri Sep 15 *)
(* transferred from Proc.v --- why was it there? *)

Fixpoint element_at {A: Type} (l : list A) (p : nat) : option A := 
  match l with 
  | nil => None
  | h :: t =>
      match p with 
      | 0 => Some h 
      | S p' => element_at t p'
      end
  end.

Section Find.

  Variable A : Type.
  Variable P : A -> Prop.
  Variable P_dec : forall a : A, {P a} + {~P a}.

  Lemma exists_in_list_dec : forall l,
      {exists r, P r /\ In r l} + {~exists r, P r /\ In r l}.

  Proof.
    induction l.
    right. intros H.  do 2 destruct H; simpl in H; auto.
    (* right. intuition . do 2 destruct H; simpl in H; auto. *)
    destruct (P_dec a).
    left; exists a; simpl; auto.
    destruct IHl.
    left. destruct e. exists x. simpl; tauto.
     right. intros H. do 2 destruct H. simpl in H0. destruct H0.
     (* right; intuition. do 2 destruct H. simpl in H0. destruct H0. *)
    subst; tauto. apply n0. exists x; auto.
  Defined.

  Fixpoint find_first (l: list A) : option nat := 
    match l with
    | nil => None
    | hd::tl => 
        match P_dec hd with
        | left _ => Some 0
        | right _ => 
	    match find_first tl with
            | None => None
	    | Some i => Some (S i)
	    end
        end
    end.

  Fixpoint find_last (l: list A) : option nat := 
    match l with
    | nil => None
    | hd::tl => 
        match find_last tl with
        | Some i => Some (S i)
        | None => 
	    match P_dec hd with
	    | left _ => Some 0
	    | right _ => None
	    end
        end
    end.

  Lemma find_first_ok : 
    forall l p, find_first l = Some p ->
                exists ell, (nth_error l p = Some ell /\ P ell).

  Proof.
    induction l.
    inversion 1.
    simpl.
    destruct (P_dec a).
    intros q q0.
    inversion q0.
    exists a; split; trivial.
    destruct p.
    destruct (find_first l); inversion 1.
    intros pl.
    destruct (IHl p) as [ell [lp Pl]].
    destruct (find_first l); inversion pl; trivial.
    exists ell; split; trivial.
  Qed.

  Lemma find_last_ok : 
    forall l p, find_last l = Some p ->
                exists ell, nth_error l p = Some ell /\ P ell.

  Proof.
    induction l.
    inversion 1.
    simpl.
    destruct (P_dec a).
    intros q q0.
    destruct q.
    exists a; split; trivial.
    destruct (IHl q) as [ell [lq Pel]].
    destruct (find_last l); inversion q0; trivial.
    exists ell; split; trivial.
    intros q q0.
    destruct q.
    destruct (find_last l); discriminate.
    destruct (IHl q) as [ell [lq Pel]].
    destruct (find_last l); inversion q0; trivial.
    exists ell; split; trivial.
  Qed.

  Lemma find_last_last: 
    forall l p ell, nth_error l p = Some ell -> P ell ->
                                       exists q, find_last l = Some q /\ q >= p.

  Proof.
    induction l; intros.
    destruct p; inversion H.
    destruct p.
    inversion H.
    simpl; destruct (P_dec ell).
    destruct (find_last l).
    exists (S n); split; [trivial | lia].
    exists 0; split; [trivial | lia].
    absurd (P ell); trivial. 
    destruct (IHl p ell) as [w [lw wp]]; trivial.
    exists (S w); split.
    simpl; rewrite lw; trivial.
    lia.
  Qed.

  Lemma find_first_exist :
    forall x l, In x l -> P x -> find_first l <> None.
  
  Proof. 
    intros. induction l. simpl in H;tauto.
    simpl in H. destruct H. subst; simpl.
    destruct (P_dec x); auto; discriminate.
    simpl. destruct (P_dec a). discriminate.
    pose proof (IHl H). 
    destruct (find_first l). discriminate. tauto.
  Qed.


  Lemma find_first_Some : forall l,
      find_first l <> None -> exists z, In z l /\ P z.

  Proof.
    intros.
    induction l.
    simpl in H; tauto.
    simpl in H. destruct (P_dec a).
    exists a; split; simpl; tauto.
    destruct (find_first l); try discriminate.
    assert (exists z : A, In z l /\ P z).
    apply IHl; discriminate.
    destruct H0. exists x.
    simpl; tauto.
    tauto.
  Qed.

  Lemma find_first_Some_bound : forall l x,
      find_first l = Some x -> x < List.length l.

  Proof.
    induction l; intros.
    simpl in H; discriminate.
    simpl in H. destruct (P_dec a).
    inversion H; subst.
    simpl; lia.
    destruct (find_first l).
    inversion H; subst.

    simpl; apply lt_n_S; apply IHl; auto.

    discriminate.
  Qed.

  Lemma In_find_first2 : forall l z,
      find_first l = Some z -> exists y, element_at l z = Some y /\ P y.
  (* find_first l = Some z -> exists y, l [ z ] = Some y /\ P y. *)

  Proof.
    induction l; intros; simpl in H. discriminate; tauto.
    destruct (P_dec a).
    inversion H; subst. exists a; simpl; split; auto.
    destruct (find_first l); try discriminate; try tauto.
    inversion H.
    now apply IHl.
  Qed.

  Lemma find_first_exact : forall l i,
      find_first l = Some i -> exists z, element_at l i = Some z /\ P z.

  Proof.
    induction l; intros. simpl in H. discriminate.
    simpl in H. destruct (P_dec a).
    inversion H. exists a; subst; simpl; tauto.
    destruct (find_first l); try discriminate.
    inversion H; subst. simpl. apply IHl; auto.
  Qed.

End Find.

Arguments In_find_first2 [A P P_dec l z] _.

Section Find_more.

  Variable A : Type.
  Variables P Q : A -> Prop.
  Variable P_dec : forall a : A, {P a} + {~P a}.
  Variable Q_dec : forall a : A, {Q a} + {~Q a}.

  Variable eq_dec : forall x y : A, {x=y} +{~x=y}.

  Lemma eq_In_find_first : 
    forall x l, In x l ->
                exists z, @find_first A (eq x) (eq_dec x) l = Some z
                          /\ element_at l z = Some x.

  Proof.
    intros; induction l.
    unfold In in H; tauto.
    simpl in H.
    destruct (eq_dec x a); subst.
    (* exists 0; split; simpl; auto with *. *)
    exists 0; split; simpl; auto.
    destruct (eq_dec a a); auto; tauto.
    destruct H; subst; try tauto.
ded (IHl H); destruct H0 as [z]; destruct H0.
exists (S z); split; simpl; auto .
destruct (eq_dec x a); subst; try tauto.

destruct (@find_first _ _ _ l); subst; try tauto;
inversion H0; subst; auto.
Qed.

Lemma eq_find_first_exact : forall l x z,
  @find_first _ (eq x) (eq_dec x) l = Some z -> element_at l z = Some x.

Proof.
intro; intro.
induction l; intros; simpl in *. discriminate.
destruct (eq_dec x a); subst.
inversion H; subst; auto .
assert (exists i, @find_first _ (eq x) (eq_dec x) l = Some i).
destruct (@find_first _ (eq x) (eq_dec x) l); try discriminate.
exists n0; auto .
destruct H0.
ded (IHl _ H0).
rewrite H0 in H.
destruct z; inversion H; subst; hyp.
Qed.

Lemma element_at_find_first_eq : forall l x i,
 element_at l i = Some x -> exists j, j <= i /\ @find_first _ (eq x) (eq_dec x) l = Some j.

Proof.
induction l; simpl; intros. discriminate. destruct i.
inversion H. subst x. case (eq_dec a a); intro. exists 0. auto. cong.
case (eq_dec x a); intro. exists 0. split. lia. easy.
(* case (eq_dec x a); intro. exists 0. intuition. *)
destruct (IHl _ _ H). destruct H0. rewrite H1. exists (S x0). 
split. lia. easy.
Qed.

End Find_more.

Arguments find_first [A] [P] [_].

Arguments eq_In_find_first [A] _ [x l] _.
Arguments eq_find_first_exact [A eq_dec l x z] _.
Arguments element_at_find_first_eq [A] _ [l x i] _.
