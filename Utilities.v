  (* Time-stamp: <Wed 11/22/23 12:09 Dan Dougherty Utilities.v> *)
 
(* from https://coq.inria.fr/refman/changes.html

Deprecated: some obsolete files from the Arith part of the standard library (Div2, Even, Gt, Le, Lt, Max, Min, Minus, Mult, NPeano, Plus). Import Arith_base instead of these files. References to items in the deprecated files should be replaced with references to PeanoNat.Nat as suggested by the warning messages. Concerning the definitions of parity properties (even and odd), it is recommended to use Nat.Even and Nat.Odd. If an inductive definition of parity is required, the mutually inductive Nat.Even_alt and Nat.Odd_alt can be used. However, induction principles for Nat.Odd and Nat.Even are available as Nat.Even_Odd_ind and Nat.Odd_Even_ind. The equivalence between the non-inductive and mutually inductive definitions of parity can be found in Nat.Even_alt_Even and Nat.Odd_alt_Odd. All Hint declarations in the arith database have been moved to Arith_prebase and Arith_base. To use the results about Peano arithmetic, we recommend importing PeanoNat (or Arith_base to base it on the arith hint database) and using the Nat module. Arith_prebase has been introduced temporarily to ensure compatibility, but it will be removed at the end of the deprecation phase, e.g. in 8.18. Its use is thus discouraged. (#14736, #15411, by Olivier Laurent, with help of Karl Palmskog).
*)

From Coq Require Export Bool.
From Coq Require Export Strings.String.
From Coq Require Export Lists.List. Export ListNotations.
From Coq Require Export ListSet.
From Coq Require Export Arith_base.
From Coq Require Export Nat.
From Coq Require Export PeanoNat.
From Coq Require Export Logic.FunctionalExtensionality.
From Coq Require Export Lia.

From Coq Require Import 
  Classical_Prop
  FunctionalExtensionality
  PropExtensionality.

From Equations Require Export Equations.

From RC Require Import 
  Decidability
  CpdtTactics
.

(** Haskell-like paren avoidance *)

Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing).

Definition rel (X Y : Type) := X -> Y -> Prop.
Definition relb (X Y : Type) := X -> Y -> bool.

(** * Tactics *)

Ltac hyp := assumption || (symmetry; assumption).
Ltac ehyp := eassumption.
Ltac refl := reflexivity.
Ltac sym := symmetry.
Ltac trans x := transitivity x.
Ltac contr := contradiction.
Ltac cong := congruence.
Ltac discr := intros; discriminate.
(* Ltac fo := unfold flip, impl; firstorder. *)
Ltac gen t := generalize t.
Ltac ded t := gen t; intro.
(* Ltac class := fold impl; auto with typeclass_instances. *)
Ltac decomp h := decompose [and or ex] h; clear h.
Ltac inv H := inversion H; subst.

Ltac dest t e := destruct t eqn: e.

(** *** N-ary Conjunctions and Disjunctions *)
(** from Arthur Chargueraud LibTactics*)

Ltac splits_tactic N :=
  match N with
  | O => fail
  | S O => idtac
  | S ?N' => split; [| splits_tactic N']
  end.

(** [generalizes X] is a shorthand for calling [generalize X; clear X].
    It is weaker than tactic [gen X] since it does not support
    dependencies. It is mainly intended for writing tactics. *)

Tactic Notation "generalizes" hyp(X) :=
  generalize X; clear X.
Tactic Notation "generalizes" hyp(X1) hyp(X2) :=
  generalizes X1; generalizes X2.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) :=
  generalizes X1 X2; generalizes X3.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) hyp(X4) :=
  generalizes X1 X2 X3; generalizes X4.

(** *** Sorting Hypotheses *)

(** [sort] sorts out hypotheses from the context by moving all the
    propositions (hypotheses of type Prop) to the bottom of the context. *)

Ltac sort_tactic :=
  try match goal with H: ?T |- _ =>
  match type of T with Prop =>
    generalizes H; (try sort_tactic); intro
  end end.

Tactic Notation "sort_context" :=
  sort_tactic.


(** * Little definitions and lemmas *)

Definition pred_strong : forall (n: nat), 
    n > 0 -> {m :nat | n = S m}.
Proof.
  intros n H.
  destruct n as [| n'] eqn:e.
  - apply False_rec. inversion H.
  - now exists n'.
Qed.
    

(* this used to be in standard library, in Arith.Lt but that file is
deprecated.  Proved here since I use it in a few places *)

Theorem lt_n_S n m : n < m -> S n < S m.
Proof.
 apply Nat.succ_lt_mono.
Qed.


(** map a function over a pair *)
Definition map_pair {A B : Type} (f : A -> B)  (p: prod A A) :=
  (f (fst p), f (snd p)).

 
Inductive pullB {A} (f: A -> bool) : list A -> A -> list A -> Prop :=
| PullHead: forall a xs,
    f a = true ->
    pullB f (a :: xs) a xs
| PullTail: forall x a xs ys,
    pullB f xs a ys ->
    pullB f (x :: xs) a (x :: ys).


(** *** options and well foundedness *)

 Inductive opt_mapR {X Y : Type} (r: X -> Y -> Prop) :
  option X -> option Y -> Prop :=
| opt_mapRNone : opt_mapR r None None
| opt_mapRSome x y :
  r x y -> opt_mapR r (Some x) (Some y).
Global Hint Constructors opt_mapR : core.



(** Mapping a relation into the option mondad preserves well_foundedness
*)

Section Option_Well_Founded .
Variable  T : Type.
Variable R : T -> T -> Prop.

Hypothesis R_is_wf : well_founded R.

Inductive opt_order : (option T) -> (option T) -> Prop :=
  | lt_ab  (y:T) : opt_order None (Some  y)
  | lt_bb (x y:T) : R x y -> opt_order (Some x) (Some y).

Lemma acc_None : Acc opt_order None.
 Proof.  
   split; intros y H; inversion H.
 Qed.

Lemma acc_Some :
    forall x:T, Acc R x -> Acc opt_order (Some x).
  Proof.
    intros x HaccT.    
    induction HaccT.
    apply Acc_intro; intros y H3.
    inversion H3.  
    + apply acc_None.
    + auto.  
  Qed.

Lemma opt_order_is_wf : well_founded opt_order.
Proof.
  unfold well_founded.
  intros.
  destruct a eqn:e.  all: revgoals.
  - apply acc_None.
  - apply acc_Some.
    apply R_is_wf.
Qed.


End Option_Well_Founded.

Arguments opt_order {T}.
Arguments opt_order_is_wf {T}.




(** Compose two binary relations 

NOTE: diagrammatic order, opposite from functions *)

Inductive composeR
  {X Y Z: Type} (rXY: X -> Y -> Prop) (rYZ : Y -> Z -> Prop)
  : X -> Z -> Prop :=
| C_composeR x y z :
  rXY x y -> 
  rYZ y z -> 
  composeR rXY rYZ x z.


(** Compose a relation with a function.  Function is applied second  *)

Inductive composeRF 
  {X Y Z: Type} (r: X -> Y -> Prop) (f : Y -> Z)
  : X -> Z -> Prop :=
| C_composeRF x y :
  r x y ->
  composeRF r f x (f y)
.

Definition rel_of {X Y: Type} (f: X -> Y) : rel X Y :=
  fun x y => (f x) = y.

Lemma composeRF_composeR_iff
  {X Y Z: Type} (r: X -> Y -> Prop) (f : Y -> Z) 
  (x: X) (z: Z) :
     composeRF r f x z <-> 
       composeR r (rel_of f) x z.

Proof.
  split.
  - intros H .
    inv H.
    econstructor; eauto. now unfold rel_of.
  - intros H. inv H. unfold rel_of in *.
    rewrite <- H1. now constructor.
Qed.

Lemma composeRF_composeR
  {X Y Z: Type} (r: X -> Y -> Prop) (f : Y -> Z) :
     composeRF r f =  
       composeR r (rel_of f) .
Proof.
apply functional_extensionality; intros e. 
apply functional_extensionality; intros d. 
apply propositional_extensionality.
apply composeRF_composeR_iff.
Qed.


Definition one_of_two (P1 P2: Prop) : Prop :=
  (P1 \/ P2) /\
    (~ (P1 /\ P2)) .

Definition one_of_three (P1 P2 P3: Prop) : Prop :=
  (P1 \/ P2 \/ P3) /\
    (~ (P1 /\ P2)) /\
    (~ (P2 /\ P3)) /\
    (~ (P1 /\ P3)).


(* ====================================== *)
(* ====================================== *)
(** * Monads *)

Class Monad (m:Type -> Type) := 
{
  ret : forall {A:Type}, A -> m A ; 
  bind : forall {A B:Type}, m A -> (A -> m B) -> m B
}.

(** More natural than bind, sometimes *)
Definition lft {M: Type -> Type} {_ : Monad M} {A B: Type}(f : A -> M B) (a : M A) : M B :=
  bind a f.


Notation "'letM' x ':=' c1 'in' c2" := 
  (bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) .

Notation "a >>= f" :=  (bind a f) (at level 42, left associativity).

Notation "f =<< a" :=  (bind a f) (at level 50, left associativity).
 


(* ============================================= *)
(** ** Option *)

(** *** Option is a monad *)

#[global]
Instance OptionMonad : Monad option := 
{
  ret := fun {A:Type} (x:A) => Some x ; 
  bind := fun {A B:Type} (x:option A) (f:A -> option B) =>
            match x with 
              | None => None
              | Some y => f y
            end
}.


Definition is_Someb {T: Type} (o: option T) : bool :=
  match o with 
    None => false | Some _ => true
end.

Definition is_Some {T: Type} (o: option T) : Prop :=
  exists t, o = Some t.

(** Extract all the [x] such that [Some x] is in l *)
Fixpoint extract_somes {X: Type} (l: list (option X)) : list X :=
  match l with 
  | [] => []
  | (Some x) :: rest => x :: (extract_somes rest)
  | None :: rest => (extract_somes rest)
end.


Section OptionLemmas.

Variable T : Type.
Variable ot : option T.

Lemma not_None_is_Some :
  (ot <> None) ->
  is_Some ot.
Proof.
  intros H.
  destruct ot eqn:oeq.
  - exists t. easy.
  - congruence.
Qed.

Lemma not_None_Some :
  (ot <> None) ->
    exists t, ot = Some t.
Proof.
  intros H.
  destruct ot eqn:oeq.
  - exists t. easy.
  - congruence.
Qed.

Lemma Some_not_None :
    (exists t, ot = Some t) ->
    (ot <> None).
Proof.
  intros.
  destruct H as [t E].
  rewrite E. congruence.
Qed.

Lemma is_Some_not_None :
  is_Some ot ->
  (ot <> None).
Proof.
  intros.
  destruct H as [t E].
  rewrite E. congruence.
Qed.

Lemma some_none :
  is_Some ot <->
  (ot <> None).
Proof.
split.
apply is_Some_not_None.
apply not_None_is_Some.
Qed.


End OptionLemmas.


(** thanks: John Ramsdell *)

Lemma do_some:
  forall A B (f: option A) (g: A -> option B) b,
    (letM x := f in g x = Some b) ->
    exists a, f = Some a /\ g a = Some b.
Proof.
  intros.
  destruct f as [x|].
  - exists x; auto.
  - inversion H.
Qed.


Fixpoint map_opt' {A B} (f: A -> option B) (l: list A): option (list B) :=
  match l with
  | [] => Some []
  | x :: xs =>
    letM y := f x in
    letM ys := map_opt' f xs in 
    Some (y :: ys)
  end.

Lemma map_opt'_nil:
  forall A B (f: A -> option B) x xs,
    map_opt' f (x :: xs) <> Some [].
Proof.
  intros.
  intro.
  simpl in H.
  apply do_some in H.
  destruct H as [y H].
  destruct H as [H G].
  apply do_some in G.
  destruct G as [ys G].
  destruct G as [G F].
  inversion F.
Qed.

Lemma map_opt'_pair:
  forall A B (f: A -> option B) x xs y ys,
    map_opt' f (x :: xs) = Some (y :: ys) ->
    f x = Some y /\ map_opt' f xs = Some ys.
Proof.
  intros.
  simpl in H.
  apply do_some in H.
  destruct H as [z H].
  destruct H as [H G].
  apply do_some in G.
  destruct G as [zs G].
  destruct G as [G F].
  inversion F; subst; auto.
Qed.

Fixpoint fold_opt {A B} (f: A -> B -> option A)
         (a: A) (l: list B): option A :=
  match l with
  | [] => Some a
  | x :: xs =>
    letM b := f a x in
    fold_opt f b xs
  end.


(** ** A more informative option type *)

Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).
Arguments SomeE {X}.
Arguments NoneE {X}.

(** *** optionE is a monad *)

#[global]
Instance OptionEMonad : Monad optionE := 
{
  ret := fun {A:Type} (x:A) => SomeE x ; 
  bind := fun {A B:Type} (x: optionE A) (f: A -> optionE B) =>
            match x with 
              | NoneE s => NoneE s
              | SomeE y => f y
            end
}.
(**  Decidability of equality of opt
*)
#[export] Instance eqDecision_optionE 
  {A  : Type}`{EqDecision A} :
  EqDecision (optionE A ).
Proof.
 unfold EqDecision. intros . 
 solve_decision.
 apply string_eq_dec.
Defined.

Lemma not_NoneE_SomeE {X: Type} (ot: optionE X) :
  (forall s, (ot <> NoneE s )) ->
    exists t, ot = SomeE t.
Proof.
  intros H.
  destruct ot eqn:oeq.
  - exists x. easy.
  - specialize (H s).
congruence.
Qed.



Inductive oE_lift {X: Type} (r : X -> Prop) : 
  optionE X -> Prop :=
  | oE_lift_1 m :  oE_lift r (NoneE m)
  | oE_lift_2 st :  
    r st -> oE_lift r (SomeE st)
.
#[export] Hint Constructors oE_lift : core. 
#[export] Instance oE_lift_dec 
  {X: Type} (r : X -> Prop) `{forall x, Decision (r x)} :
  forall (ox: optionE X),
    (Decision (oE_lift r ox)).
Proof.
  intros. 
  destruct ox eqn:e.
  destruct (decide (r x)).
  { left; now constructor.
  }
  { right; intros F; now inv F.
  } 
  left; now constructor.
Defined.


(** General exception type *)
Inductive opt (A B : Type) : Type :=
| ok: A -> opt A B
| exn: (list string) -> B -> opt  A B.

(* note use of string_scope for errmsg argument *)
Arguments opt _%type_scope.
Arguments ok {A B} %type_scope.
Arguments exn {A B} %type_scope s%string_scope.


(**  Decidability of equality of opt
*)
#[export] Instance eqDecision_opt 
  {A B : Type}`{EqDecision A} `{EqDecision B} :
  EqDecision (opt A B).
Proof.
 unfold EqDecision. intros . 
 solve_decision.
 (* (try apply exp_eq_dec); *)
 (*   (try apply term_eq_dec); *)
 (* (try apply eqDecision_bnd). *)
 (* apply list_eq_dec with string_beq. *)
apply list_eq_dec. 
Defined.

(** Maybe *)

(** ** not actually a monad but close.
Ack: Adam Chlipala  *)

Inductive maybe {A : Set} (P : A → Prop) : Set := 
| Found: forall (x: A) ,  P x -> maybe P
| Unknown : maybe P
.

Notation "{{ x | P }}" := (maybe (fun x => P)).

Notation "'letY' x ':=' e1 'in' e2" :=
  (match e1 with
   | Unknown _  => Unknown
   | Found _ x _  => e2 
   end)
(right associativity, at level 60).

(* The meaning of [letY x := e1 in e2] is: First run e1. If it fails
to find an answer, then announce failure for our derived computation,
too. If e1 does find an answer, pass that answer on to e2 to find the
final result. The variable x can be considered bound in e2.  *)


Section MaybeProofs.
Variable A X: Set.
Variable P : A -> Prop.

(** intuitively have f : X -> A

and want to claim P holds of a successful result

*)

Variable fM : X -> {{ x | P x}}.
 
Definition maybe_opt (x: X) : option A :=
  match (fM x) with
    Found _ a _ => Some a
  | Unknown _ => None
end.

Lemma maybe_opt_proof (x: X) :
  forall a, maybe_opt x = Some a -> P a.
Proof.
  intros a H;
  unfold maybe_opt in H;
  destruct (fM x) eqn:e; 
  congruence.
Qed.

End MaybeProofs.


(** Return the first (f x) that is different from x  *)
Fixpoint apply_first_neqb 
  {X : Type} {_ : EqbDec X} (fns: list (X -> X)) (x : X) :=
  match fns with 
    [] => x
  | f:: rest => if beq (f x) x 
                then apply_first_neqb rest x
                else (f x)
  end.
Arguments apply_first_neqb {X} {beq}.

Fixpoint apply_first_neqP 
  {X : Type} {_ : EqDecision X} (fns: list (X -> X)) (x : X) :=
  match fns with 
    [] => x
  | f:: rest =>
      match (decide ((f x) = x)) with
        | left _ => apply_first_neqP rest x
      |  right _ => (f x)
  end
  end.
Arguments apply_first_neqP {X} {_}.


(** Return the first [f x] that is not [] *)
Fixpoint apply_first_not_nil
  {X Y : Type}  (fns: list (X -> (list Y))) (x : X) : list Y
  :=  match fns with 
        [] => []
      | f:: rest => if (f x) 
                    then apply_first_not_nil rest x
                    else (f x)
  end.

(** extracting the value from a sig type *)
(* WAIT - how does this differ from [proj1_sig] ?? *)

Definition proj_sig {X} {P} (s : @sig X P) :=
   match s with
     (exist _ x _) => x
   end.

Section SumorProofs.
Variable A X: Set.
Variable P : A -> Prop.

(** intuitively have f : X -> A

and want to claim P holds of a successful result

*)

Variable fM : X -> { x: A | P x} + {True}.
 
Definition sumor_opt (x: X) : option A.
  destruct  (fM x) as [ [s H] | Q].
  - exact (Some s).
  - exact None.
Defined.

Lemma sumor_opt_proof (x: X) :
  forall a, sumor_opt x = Some a -> P a.
Proof.
  unfold sumor_opt.
  intros a H.
  destruct (fM x) eqn:e. 
  destruct s as [x0 Q].
  - congruence.
  - congruence.
Qed.

End SumorProofs.



(* ****************************************************** *)
(* * Showing *)
(* ****************************************************** *)
Open Scope string_scope.

Fixpoint catstrings (ss: list string) : string := 
  match ss with 
    nil => ""
  | cons h nil => h
  | cons h rest =>  h ++ ", " ++ (catstrings rest)
  end.

Class Show A : Type :=
  { show : A -> string }.


(** it's funny that we have to do this *)
#[export] Instance show_string : Show string :=
  {show := fun v => v}.

(* -------------------------------------------------------- *)
(** from Software Foudations (v4, module Typeclasses *)

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

#[export] Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.

(** Taken from Software Foundations (slight tweak) *)

Fixpoint showListAux {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""
    | cons h nil => s h
    | cons h t => append (append (s h) "; ") (showListAux s t)
  end.

Fixpoint showListElements {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""
    | cons h nil => s h
    | cons h t => append (append (s h) ", ") (showListElements s t)
  end.

(** just concat list elements together, no spacing *)

Fixpoint catListElements {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""
    | cons h nil => s h
    | cons h t => (append (s h)(catListElements s t))
  end.

#[global] Instance showList {A : Type} `{Show A} : Show (list A) :=
  {
    show l := append "[" (append (showListElements show l) "]")
  }.

#[global] Instance showOption {A : Type} `{Show A} : Show (option A) :=
  {
    show x := 
      match x with
        None => "None"
      | Some a => "Some " ++ (show a)
      end}.

Close Scope string_scope.
