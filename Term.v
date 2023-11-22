(* Time-stamp: <Wed 11/22/23 11:33 Dan Dougherty Term.v> *)

(* Starting point is the treatment of algebraic (ie symbolic) terms in
   CPSA, expressed in Coq code by John Ramsdell.

Some changes/additions made by Dan Dougherty 2022-23
*)

From Coq Require Import FunInd Nat Bool DecBool String List Arith.
Import ListNotations.

From RC Require Import
  CpdtTactics
  Utilities
  ListUtil
  Decidability
  Sorts
.


Notation var := nat (only parsing).

Definition decl: Set := var * sort.

Global Instance decl_eq_dec : EqDecision decl.
Proof. solve_decision. solve_decision. Defined.

(** Symmetric keys *)

Inductive skey: Set :=
| Sv: nat -> skey               (* Variable as key *)
| Lt: nat -> nat -> skey.       (* Long term key of two names *)

(** Asymmetric keys *)

Inductive akey: Set :=
| Av: nat -> akey               (* Variable as key *)
| Pb: nat -> akey               (* Public key of name *)
| Pb2: string -> nat -> akey.   (* Tagged public key of name *)


(** Message algebra *)

Inductive Term : Set :=
| Tx: nat -> Term               (* Text *)
| Dt: nat -> Term               (* Data *)
| Nm: nat -> Term               (* Name *)
| Sk: skey -> Term              (* Symmetric key *)
| Ak: akey -> Term              (* Public key *)
| Ik: akey -> Term              (* Private key *)
| Mg: nat -> Term               (* Message *)
| Qt: string -> Term            (* Quot *)
| Pr: Term -> Term -> Term      (* Pair *)
| En: Term -> Term -> Term      (* Encyption *)
| Hs: Term -> Term              (* Hash *)
| Ch: nat -> Term               (* Channel *)
.
Notation Terms := (list Term).


(* ==================================== *)
(** * Equality *)

(* ------------------------- *)

Scheme Equality for skey.
(* now have skey_beq and  skey_eq_dec *)

(** register in EqDecision *)
#[export] Instance _skey_eq_dec : EqDecision skey.
Proof.  exact skey_eq_dec.
Defined.
 

(** establish reflection *)
Lemma skey_reflect :  
  forall (x y : skey), reflect (x = y) (skey_beq x y).
Proof.
  intros x y;
  apply iff_reflect; split.
  apply internal_skey_dec_lb.
  apply internal_skey_dec_bl.
Qed.

 (* ------------------------- *)

Scheme Equality for akey. 

(* register in EqDecision *)
#[export] Instance _akey_eq_dec : EqDecision akey
  := akey_eq_dec.

(* Check internal_akey_dec_lb. *)
Lemma akey_reflect :  
  forall (x y : akey), reflect (x = y) (akey_beq x y).
Proof.
  intros x y;
  apply iff_reflect; split.
  apply internal_akey_dec_lb.
  apply internal_akey_dec_bl.
Qed.

#[global] Instance eqbdec_akey :
  EqbDec akey
  := EqbDec_of_eq_dec akey_eq_dec.


(* ---------------------------- *)
(** *** Equality for Term *)

(** Defines 
 [Term_beq] and
 [Term_eq_dec : ∀ x y : Term, {x = y} + {x ≠ y}] *)
Scheme Equality for Term.

(** Thus Term is decidable *)

#[export] Instance term_eqDec : EqDecision Term
  := Term_eq_dec.

(** The Scheme internal functions let us make Term an instance of
[Decidability.EqbDec] *)

Lemma beq_eq_Term : forall x y, 
if Term_beq x y then x = y else x <> y.
Proof.
 intros.
 assert (abl := @internal_Term_dec_bl x y).
 assert (alb := @internal_Term_dec_lb x y).
 destruct (Term_beq x y); auto. intros F. 
 firstorder; easy.
Qed.

#[global] Instance Term_eqbdec : EqbDec (Term) :=
  { beq:= Term_beq;
    beq_eq := beq_eq_Term
  }.
  
(** Since Term is a [Decidability.EqbDec], we have reflection,
    [Decidability.beq_reflect]
 *)

(* ------------------------------ *)
(** Equality for lists of Term *)

#[export] Instance Terms_eq_dec :
  EqDecision (list Term).
Proof. apply list_eq_dec.
Defined.


(* CAREFUL...nervous about creating a bool out of a Prop this way...have we reall done anything?
*)
#[global] Instance Terms_eqbdec :
  EqbDec (list Term)
  := EqbDec_of_eq_dec Terms_eq_dec.

Lemma Terms_reflect :  
  forall (x y : Terms), reflect (x = y) (beq x y).
Proof. exact Decidability.beq_reflect.
Qed.


(* ------------------------- *)
(** ** Determinism *)

(* When nondeterministic encryption is used, terms that carry
encryptions will not have their runtime denotations uniqely determined

*)

Fixpoint nondeterministic (t: Term) : bool :=
  match t with
  | En p k  => true
  | Pr t1 t2 => nondeterministic t1 || nondeterministic t2
  | Hs t1 => nondeterministic t1
  | _ => false
  end.

Equations deterministic (t: Term) : bool :=
  deterministic (En p k) := 
    false;
  deterministic (Pr t1 t2) := 
    deterministic t1 && deterministic t2;
  deterministic (Hs t1) :=
    deterministic t1;
  deterministic _ := true
.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(** ** Inverse of a Message *)


(** *** Dolev-Yao symbolic inverse.
    
Compare strict_inverse below.

 When symmetric encryption is nondeterministic,
syntactically equal symbolic term occurences don't guarantee actual
runtime equality. *)

Definition inv (x: Term): Term :=
  match x with
  | Ak k => Ik k
  | Ik k => Ak k
  | k => k
    end.
Arguments inv /.

Lemma inv_inv:
  forall (x: Term),
    inv (inv x) = x.
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Lemma inv_swap:
  forall (x y: Term),
    x = inv y <-> y = inv x.
Proof.
  split; intros; subst;
    rewrite inv_inv; auto.
Qed.

(** As a binary relation *)

Definition are_inv (x y: Term) : Prop :=
  (inv x) = y. 

#[export] Hint Unfold are_inv : core.

#[export] Instance are_inv_dec :
  forall t1 t2, Decision (are_inv t1 t2).
Proof. intros t1 t2.
       apply Term_eq_dec.
Defined.

Definition are_invb (x y: Term) : bool :=
   sumbool_to_bool (are_inv_dec x y).

Lemma are_inv_t_inv (t: Term) :
  are_inv t (inv t).
Proof.
  destruct t; simpl; auto.
Qed.
#[export] Hint Resolve are_inv_t_inv : core.

Lemma are_inv_inv_t (t: Term) :
  are_inv (inv t) t.
Proof.
  destruct t; simpl; auto.
Qed.
#[export] Hint Resolve are_inv_inv_t : core.

Lemma are_inv_then_inv (t1 t2: Term) :
  are_inv t1 t2 ->
  t2 = inv t1.
Proof.
  intros H.
  destruct t1; simpl; auto.
Qed.
#[export] Hint Resolve are_inv_then_inv : core.

 
Definition makes_key_pair (x y : Term) : bool :=
  match x, y with
  | (Ik k), (Ak k') => akey_beq k k'
  | _ , _ => false
  end.

Lemma key_pair_are_inv (x y : Term) :
  makes_key_pair x y = true ->
  are_inv x y.
Proof.
  intros H.
  destruct x, y; simpl; auto;  inv H.
  unfold are_inv. 
    destruct (akey_reflect a a0).
    +  now subst.
    + easy. 
Qed.

 
(** Does k have its inverse in [ts] ? *)
Definition has_inv_in
  (ts: Terms) (k: Term) : Prop :=
  exists k', In k' ts /\ are_inv k k'.
(* *)


#[export]Instance has_inv_in_dec :
  forall ts k, Decision (has_inv_in ts k).
Proof. intros ts k.
       apply list_exists_dec.
       apply are_inv_dec.       
Defined.



(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(** ** Utilities *)
(* ========================================= *)

(** * Kinds of Messages *)

Definition is_akey (t: Term) : bool :=
  match t with
  | Ak _ => true
  | Ik _ => true
  | _ => false
  end.

(** Is [x] a basic value? *)

Definition is_basic (x: Term): bool :=
  match x with
  | Tx _ => true
  | Dt _ => true
  | Nm _ => true
  | Sk _ => true
  | Ak _ => true
  | Ik _ => true
  | _ => false
  end.

(** Is [x] a channel ? *)

Definition is_chan (x: Term): bool :=
  match x with
  | Ch _ => true
  | _ => false
  end.

(** Is [x] a message ? *)

Definition is_mesg_var (x: Term): bool :=
  match x with
  | Mg _ => true
  | _ => false
  end.

(** Is [x] a simple message, one that is not a pair, encryption, or a
    hash? *)

Definition is_simple (x: Term): bool :=
  match x with
  | Pr _ _ => false
  | En _ _ => false
  | Hs _ => false
  | _ => true
  end.

(** Is [x] an elementary message, one that is not a pair, encryption, a
    hash, or a tag? *)

Definition is_elementary (x: Term): Prop :=
  match x with
  | Pr _ _ => False
  | En _ _ => False
  | Hs _ => False
  | Qt _ => False
  | _ => True
  end.


#[export] Instance elementary_dec : 
  forall t,
    (Decision (is_elementary t)).
Proof. intros t.
       unfold Decision.
       destruct t eqn:e1.
       all: try (left; simpl; easy) .
       all: right; simpl; easy.
Defined.

(** Is [x] not an elementary message? *)

Definition is_not_elementary (x: Term): Prop :=
  match x with
  | Pr _ _ => True
  | En _ _ => True
  | Hs _ => True
  | Qt _ => True
  | _ => False
  end.

Definition is_elementaryb (x: Term): bool :=
  match x with
  | Pr _ _ => false
  | En _ _ => false
  | Hs _ => false
  | Qt _ => false
  | _ => true
  end.

Definition is_not_elementaryb (x: Term): bool :=
  match x with
  | Pr _ _ => true
  | En _ _ => true
  | Hs _ => true
  | Qt _ => true
  | _ => false
  end.

(** The "elementary" subterms of a term.
    This INCLUDES keys of encryptions
 *)

Fixpoint elems_of_term (t: Term) : Terms :=
  nodup Term_eq_dec
    (match t with
     | Qt s => []
     | Pr t1 t2 => elems_of_term t1 ++ elems_of_term t2
     | En p k  => elems_of_term p ++ elems_of_term k
     | Hs t1 => elems_of_term t1
     | _ => [t]
     end).

Fixpoint elems_of_terms (ts: Terms) : Terms :=
  nodup Term_eq_dec
    (match ts with
       [] => []
     | t:: rest => elems_of_term t ++ elems_of_terms rest
     end).

Definition is_quoteP (x: Term) :=
  match x with
  | Qt _ => True
  | _  => False
end.

Definition is_quote (x: Term) : bool :=
  match x with
  | Qt _ => true
  | _  => false
end.

Lemma is_quoteP_dec:
  forall x: Term, {is_quoteP x} + {~ is_quoteP x}.
Proof.
  intros.
  unfold is_quoteP.
  destruct x; auto.
Qed.


Definition pair_analyze (t: Term) : option (Term*Term) :=
  match t with 
    Pr t1 t2 => Some (t1, t2)
  | _ => None
end.

Lemma pair_analyze_ok t t1 t2 :
  pair_analyze t  = Some (t1 , t2) ->
  t = (Pr t1 t2).
Proof.
  intros.
  destruct t eqn:e; inv H. easy.
Qed.


(** a maybe-useful induction principle
*)
Lemma term_elem_ind:
  forall P: Term -> Prop,
    (forall x: Term, is_elementary x -> P x) ->
    (forall s: string, P (Qt s)) ->
    (forall y: Term,
        P y ->
        forall z: Term,
          P z -> P (Pr y z)) ->
    (forall y: Term,
        P y ->
        forall z: Term, P (En y z)) ->
    (forall y: Term,
        P y -> P (Hs y)) ->
    forall x: Term, P x.
Proof.
  intros.
  induction x; simpl; auto; apply H; simpl; auto.
Qed.

(** ** Sort of a  Term *)

Definition sort_of (x: Term): sort :=
  match x with
  | Tx _ => Text
  | Dt _ => Data
  | Nm _ => Name
  | Sk _ => Skey
  | Ak _ => Akey
  | Ik _ => Ikey
  | Ch _ => Chan
  | _ => Mesg
  end.

Lemma same_inv_not_akey (t: Term) :
  inv t = t ->
  is_asym_key_sort (sort_of t) = false.
Proof. 
  intros H.
  destruct t eqn:et; simpl in H; simpl; auto.
  inv H. inv H.
Qed.


Lemma simple_inv_simple (k: Term) :
  is_simple k  = true ->  is_simple (inv k) = true.
Proof.
  destruct k; simpl; auto.
Qed.
Lemma inv_simple (k: Term) :
  is_simple k = false -> (inv k) = k.
Proof.
  destruct k; simpl; congruence.
Qed.


Lemma elementary_inv_elementary (k: Term) :
  is_elementaryb k  = true ->  is_elementaryb (inv k) = true.
Proof.
  destruct k; simpl; congruence.
Qed.

Lemma inv_elementary (k: Term) :
  is_elementaryb k = false -> (inv k) = k.
Proof.
  destruct k; simpl; congruence.
Qed.


(** ** Measure of a Term *)

Fixpoint size_term (x: Term): nat :=
  match x with
  | Pr y z => S (size_term y + size_term z)
  | En y z => S (size_term y + size_term z)
  | Hs y => S (size_term y)
  | _ => 1
  end.


Lemma inv_size_term:
  forall x, size_term (inv x) = size_term x.
Proof.
  intros.
  destruct x; simpl; auto.
Qed.




(* ==================================== *)
(** * Showing symbolic Terms *)

Open Scope string_scope.

#[export] Instance showVar : Show var :=
  {show := fun v => show v}.
  (* {show := fun v => "x" ++ show v}. *)

(** @@ FIXME case for Lt is wrong here...*)

#[export] Instance showSkey : Show skey :=
  {show := fun k =>
             match k with
             | Sv x => show x
             | Lt x y => "(Lt " ++ (show x) ++ " " ++ (show y) ++ ")"
             end
}.

#[export] Instance showAkey : Show akey :=
  {show := fun k =>
             match k with
             | Av x => show x
             | Pb x => show x
             | Pb2 s x =>  "(Pb " ++ s ++ " " ++ (show x) ++ ")"
             end
}.

(* MAYBE
 | Pr t1 t2 => "<" ++ term_to_string t1 ++ " , " ++ term_to_string t2 ++ ">"

  | En p k   => "{|" ++ term_to_string p ++ "|}_" ++ "(" ++ (term_to_string k) ++ ")"

  | Hs t1 => "#" ++ term_to_string t1
*)
Fixpoint term_to_string (t: Term) : string :=
  match t with
  | Tx x => "(Tx " ++ show x ++ ")"
  | Dt x => "(Dt " ++ show x ++ ")"
  | Nm x => "(Nm " ++ show x ++ ")"
  | Sk k => "(Sk " ++ show k ++ ")"
  | Ak k => "(Ak " ++ show k ++ ")"
  | Ik k => "(Ik " ++ show k ++ ")"
  | Ch ch => "(Ch " ++ show ch ++ ")"
  | Mg x => "(Mg " ++ show x ++ ")"
  | Qt s => "(Qt " ++ show s ++ ")"
 
 | Pr t1 t2 => "(Pr " ++ term_to_string t1 ++ " " ++ term_to_string t2 ++ ")"

  | En p k   => "(En " ++ term_to_string p ++ " " ++  term_to_string k ++ " )"

  | Hs t1 => "(Hs "  ++ term_to_string t1 ++ ")"

  end.


#[export] Instance show_term : Show Term :=
  {show := fun v => term_to_string v
  }.

(* Coercion term_to_string : Term >-> string. *)
Close Scope string_scope.
