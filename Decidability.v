(* Time-stamp: <Wed 11/22/23 11:57 Dan Dougherty Decidability.v>

Thanks to 

- the stdpp library

- Gert Smolka's "Base" library

*)


From Coq Require Export Morphisms RelationClasses List Bool String Setoid Peano Utf8.
From Coq Require Import Permutation.
From Coq Require Import Arith. (* Includes PeanoNat *)
Export ListNotations.
From Coq.Program Require Export Basics Syntax.
Local Generalizable All Variables.

(* Pick up extra assumptions from section parameters. *)
(* Set Default Proof Using "Type*". *)


(** The following combinators are useful to create Decision proofs in
combination with the [refine] tactic. *)
Notation swap_if S := (match S with left H => right H | right H => left H end).
Notation cast_if S := (if S then left _ else right _).
Notation cast_if_and S1 S2 := (if S1 then cast_if S2 else right _).
Notation cast_if_and3 S1 S2 S3 := (if S1 then cast_if_and S2 S3 else right _).
Notation cast_if_and4 S1 S2 S3 S4 :=
  (if S1 then cast_if_and3 S2 S3 S4 else right _).
Notation cast_if_and5 S1 S2 S3 S4 S5 :=
  (if S1 then cast_if_and4 S2 S3 S4 S5 else right _).
Notation cast_if_and6 S1 S2 S3 S4 S5 S6 :=
  (if S1 then cast_if_and5 S2 S3 S4 S5 S6 else right _).
Notation cast_if_or S1 S2 := (if S1 then left _ else cast_if S2).
Notation cast_if_or3 S1 S2 S3 := (if S1 then left _ else cast_if_or S2 S3).
Notation cast_if_not_or S1 S2 := (if S1 then cast_if S2 else left _).
Notation cast_if_not S := (if S then right _ else left _).


 (* =========================================== *)

(** * Decidable propositions *)

Class Decision (P : Prop)
  := decide: {P} + {~P}.
Global Hint Mode Decision ! : typeclass_instances.
Global Arguments decide _ {_} : simpl never, assert.

#[export] Hint Unfold Decision : core.

(* Improve type class inference *)
#[export] Hint Extern 4 =>     
match goal with
  | [  |- Decision ((fun _ => _) _) ] => simpl 
end : typeclass_instances .

 (* =========================================== *)

(** * Decidable Equality *)
Class EqDecision (A : Type)
  := eq_dec : forall (x y : A),  {x=y}+{x<>y}.

#[export] Hint Extern 4  =>
match goal with
  | [  |- EqDecision ?p ] => exact (eq_dec p)
end : type_class_instances.

#[export] Hint Unfold EqDecision : core.

 (* =========================================== *)

(** * RelDecision *)

Class RelDecision {A B} (R : A → B → Prop) :=
  decide_rel x y :: Decision (R x y).
  (* decide_rel x y :> Decision (R x y). *)
Global Hint Mode RelDecision ! ! ! : typeclass_instances.
Global Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.


(* ====================================== *)


(** We can convert decidable propositions to booleans. *)

Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Lemma bool_decide_reflect P `{dec : Decision P} : reflect P (bool_decide P).
Proof. unfold bool_decide. destruct dec; [left|right]; assumption. Qed.

Lemma bool_decide_decide P `{!Decision P} :
  bool_decide P = if decide P then true else false.
Proof. reflexivity. Qed.
Lemma decide_bool_decide P {Hdec: Decision P} {X : Type} (x1 x2 : X):
  (if decide P then x1 else x2) = (if bool_decide P then x1 else x2).
Proof. unfold bool_decide, decide. destruct Hdec; reflexivity. Qed.

(** * Tactics *)
(* ==================================== *)

Lemma dec_stable `{Decision P} : ~~P -> P.
Proof. firstorder. Qed.

(** @@ MINE *)
Tactic Notation "decide_t" constr(p) := 
  destruct (decide p).
Tactic Notation "decide_t" constr(p) "as" simple_intropattern(i) := 
  destruct (decide p) as i.

(** The tactic [destruct_decide] destructs a sumbool [dec]. If one of the
components is double negated, it will try to remove the double negation. *)
Tactic Notation "destruct_decide" constr(dec) "as" ident(H) :=
  destruct dec as [H|H];
  try match type of H with
  | ~~_ => apply dec_stable in H
  end.
Tactic Notation "destruct_decide" constr(dec) :=
  let H := fresh in destruct_decide dec as H.

(** The tactic [case_decide] performs case analysis on an arbitrary occurrence
of [decide] or [decide_rel] in the conclusion or hypotheses. *)
Tactic Notation "case_decide" "as" ident(Hd) :=
  match goal with
  | H : context [@decide ?P ?dec] |- _ =>
    destruct_decide (@decide P dec) as Hd
  (* | H : context [@decide_rel _ _ ?R ?x ?y ?dec] |- _ => *)
    (* destruct_decide (@decide_rel _ _ R x y dec) as Hd *)
  | |- context [@decide ?P ?dec] =>
    destruct_decide (@decide P dec) as Hd
  (* | |- context [@decide_rel _ _ ?R ?x ?y ?dec] => *)
    (* destruct_decide (@decide_rel _ _ R x y dec) as Hd *)
  end.
Tactic Notation "case_decide" :=
  let H := fresh in case_decide as H.

(** The tactic [solve_decision] uses Coq's [decide equality] tactic together
with instance resolution to automatically generate decision procedures. *)
Ltac solve_trivial_decision :=
  match goal with
  | |- Decision (?P) => apply _
  | |- sumbool ?P (~?P) => change (Decision P); apply _
  end.

Ltac solve_decision :=
  unfold EqDecision; intros; first
    [ 
      (* solve_trivial_decision *)
    (* |  *)
      unfold Decision; decide equality
      (* solve_trivial_decision  *)
    ].

(* OLD .  This caused some hanging computations *)
(* Ltac solve_decision := *)
  (* unfold EqDecision; intros; first *)
    (* [ solve_trivial_decision *)
    (* | unfold Decision; decide equality; *)
      (* solve_trivial_decision *)
    (* ]. *)


Tactic Notation "case_bool_decide" "as" ident(Hd) :=
  match goal with
  | H : context [@bool_decide ?P ?dec] |- _ =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  | |- context [@bool_decide ?P ?dec] =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.
Tactic Notation "case_bool_decide" :=
  let H := fresh in case_bool_decide as H.


Lemma decide_True {A} `{Decision P} (x y : A) :
  P -> (if decide P then x else y) = x.
Proof. destruct (decide P); tauto. Qed.

Lemma decide_False {A} `{Decision P} (x y : A) :
  ~P -> (if decide P then x else y) = y.
Proof. destruct (decide P); tauto. Qed.

Lemma decide_iff {A} P Q `{Decision P, Decision Q} (x y : A) :
  (P ↔ Q) -> (if decide P then x else y) = (if decide Q then x else y).
Proof. intros [??]. destruct (decide P), (decide Q); tauto. Qed.


(** * Instances of [Decision] *)
(*    ======================= *)

(** ** Instances of [Decision] for operators of propositional logic. *)
Global Instance True_dec: Decision True := left I.
Global Instance False_dec: Decision False := right (False_rect False).
Global Instance Is_true_dec b : Decision (Is_true b).
Proof. destruct b; simpl; apply _. Defined.

Section prop_dec.
  Context `(P_dec : Decision P) `(Q_dec : Decision Q).

  Global Instance not_dec: Decision (~P).
  Proof. refine (cast_if_not P_dec); easy . Defined.
  Global Instance and_dec: Decision (P ∧ Q).
  Proof. refine (cast_if_and P_dec Q_dec); easy. Defined.
  Global Instance or_dec: Decision (P ∨ Q).
  Proof. refine (cast_if_or P_dec Q_dec); tauto. Defined.
  Global Instance impl_dec: Decision (P -> Q).
  Proof. refine (if P_dec then cast_if Q_dec else left _); tauto. Defined.

End prop_dec.

Global Instance iff_dec `(P_dec : Decision P) `(Q_dec : Decision Q) :
  Decision (P ↔ Q) := and_dec _ _.


(** ** Some Decidable Comparisions *)
#[export]
 Instance nat_le_dec (x y : nat) : Decision (x <= y) := 
  le_dec x y.

#[export]
 Instance nat_gt_dec (x y : nat) : Decision (x > y) := 
  gt_dec x y.

Global Instance uncurry_dec `(P_dec : ∀ (x : A) (y : B), Decision (P x y)) p :
    Decision (uncurry P p) :=
  match p as p return Decision (uncurry P p) with
  | (x,y) => P_dec x y
  end.

(** ** Some classical laws for decidable propositions *)
Lemma not_and_l {P Q : Prop} `{Decision P} : ~(P ∧ Q) ↔ ~P ∨ ~Q.
Proof. destruct (decide P); tauto. 
Qed.

Lemma not_and_r {P Q : Prop} `{Decision Q} : ~(P ∧ Q) ↔ ~P ∨ ~Q.
Proof. destruct (decide Q); tauto. 
Qed.

Lemma not_and_l_alt {P Q : Prop} `{Decision P} : ~(P ∧ Q) ↔ ~P ∨ (~Q ∧ P).
Proof. destruct (decide P); tauto. 
Qed.

Lemma not_and_r_alt {P Q : Prop} `{Decision Q} : ~(P ∧ Q) ↔ (~P ∧ Q) ∨ ~Q.
Proof. destruct (decide Q); tauto. 
Qed.

Lemma dec_DN P : 
  Decision P -> ~~ P -> P.
Proof. unfold Decision; tauto. 
Qed.

Lemma dec_DM_impl P Q :  
  Decision P -> Decision Q -> ~ (P -> Q) -> P /\ ~ Q.
Proof. unfold Decision; tauto. 
Qed.

Lemma dec_prop_iff (P Q : Prop) : 
  (P <-> Q) -> Decision P -> Decision Q.
Proof. unfold Decision; tauto.
Defined.

(** * Instances of [EqDecision] *)
(*    ========================= *)

(** ** Connect EqDecision with Decision *)

#[export] Instance eq_dec_dec (X: Type) `{H: EqDecision X} : 
  forall (x y: X), Decision (x = y).
Proof.  exact H.
Defined.

#[export] Instance neq_dec (X: Type) `{H: EqDecision X} : 
  forall (x y: X), Decision (x <> y).
  Proof. intros x y. apply not_dec. apply H . 
  Defined.

Global Instance bool_eq_dec : EqDecision bool.
Proof. solve_decision. Defined.

Global Instance unit_eq_dec : EqDecision unit.
Proof. solve_decision. Defined.

Global Instance Empty_set_eq_dec : EqDecision Empty_set.
Proof. solve_decision. Defined.

#[export] Instance nat_eq_dec :   EqDecision nat.
Proof.  intros x y. hnf. decide equality. Defined.

#[export] Instance option_eq_dec `{EqDecision A} : EqDecision (option A). 
Proof.  
  solve_decision.
Defined.

Global Instance prod_eq_dec `{EqDecision A, EqDecision B} :
 EqDecision (A * B).
Proof. solve_decision. Defined.

Global Instance sum_eq_dec `{EqDecision A, EqDecision B} : 
  EqDecision (A + B).
Proof. solve_decision. Defined.


Global Instance list_eq_dec {X: Type}`{EqDecision X}:
  EqDecision (list X).
Proof. solve_decision. Defined.
#[export] Hint Resolve list_eq_dec : core.  (* NO EFFECT *)

(** List membership  *)
#[export] Instance list_in_dec (X : Type) (x : X) (A : list X) :  
  EqDecision X -> Decision (In x A).
Proof.
  intros D. now apply List.in_dec. 
Defined.

#[export]  Hint Unfold list_eq_dec list_in_dec : core.


(** * Instances of [RelDecision] *)
(*    ========================== *)

Definition flip_dec {A} (R : relation A) `{!RelDecision R} :
  RelDecision (flip R) := λ x y, decide_rel R y x.
(** We do not declare this as an actual instance since Coq can unify [flip ?R]
with any relation. Coq's standard library is carrying out the same approach for
the [Reflexive], [Transitive], etc, instance of [flip]. *)
Global Hint Extern 3 (RelDecision (flip _)) => apply flip_dec : typeclass_instances.


(* ========================== *)

(** ** Working with [decide] and [eq_dec] *)

Lemma eq_eq_dec (T U: Type) {_: EqDecision T} (x y: T)  (u v: U) :
  x=y ->
  (if eq_dec x y then u else v) = u.
Proof. 
  intros Heq. subst.
  destruct (eq_dec y y); congruence.
Qed.
Arguments eq_eq_dec {T U} _ x y u v.

Lemma neq_eq_dec (T U: Type) {_: EqDecision  T} (x y: T)  (u v: U) :
  x<>y ->
  (if eq_dec x y then u else v) = v.
Proof.
  intros Hneq.
  destruct (eq_dec x y); congruence.
Qed.
Arguments neq_eq_dec {T U} _ x y u v.

Lemma y_if_y_dec {U: Type} (P: Prop) {_: Decision P} (u v: U) :
  P ->
  (if decide P then u else v) = u.
Proof.
  intros Hneq.
  destruct (decide P); congruence.
Qed.
Arguments y_if_y_dec {U} P {D} u v.

Lemma n_if_y_dec {U: Type} (P: Prop) {_: Decision P} (u v: U) :
  ~ P ->
  (if decide P then u else v) = v.
Proof.
  intros Hneq.
 destruct (decide P); congruence.
Qed.
Arguments n_if_y_dec {U} P {D} u v.


(** ================================================ *)

(** * Booleans *)
(** The following coercion allows us to use Booleans as propositions. *)

(* no *)
(*  Coercion Is_true : bool >-> Sortclass. *)

Global Hint Unfold Is_true : core.
Global Hint Immediate Is_true_eq_left : core.
Global Hint Resolve orb_prop_intro andb_prop_intro : core.


(* 
Definition bool_le (β1 β2 : bool) : Prop := negb β1 || β2.
Infix "=.>" := bool_le (at level 70).
Infix "=.>*" := (Forall2 bool_le) (at level 70).
*)

Lemma andb_True b1 b2 : b1 && b2 = true ↔ b1 = true  ∧ b2 = true.
Proof. destruct b1, b2; simpl; tauto. Qed.

Lemma orb_True b1 b2 : b1 || b2 = true  ↔ b1 = true ∨ b2 = true.
Proof. destruct b1, b2; simpl; tauto. Qed.


Lemma negb_True b : negb b  = true <-> ¬ (b  = true).
Proof. split; destruct b; simpl; congruence.
Qed.

Lemma Is_true_false (b : bool) : ¬ (b = true)  ↔ b = false.
Proof. now destruct b; simpl. Qed.

Lemma Is_true_false_1 (b : bool) : ¬ (b = true) → b = false.
Proof. apply Is_true_false. Qed.

Lemma Is_true_false_2 (b : bool) : b = false → ¬ (b = true).
Proof. apply Is_true_false. Qed.

Lemma bool_decide_spec (P : Prop) {dec : Decision P} : bool_decide P = true ↔ P.
Proof. unfold bool_decide. destruct dec; simpl.  tauto. 
       split. intros. congruence. intros. congruence. Qed.
Lemma bool_decide_unpack (P : Prop) {dec : Decision P} : bool_decide P = true -> P.
Proof. rewrite bool_decide_spec; trivial. Qed.
Lemma bool_decide_pack (P : Prop) {dec : Decision P} : P -> bool_decide P = true.
Proof. rewrite bool_decide_spec; trivial. Qed.
Global Hint Resolve bool_decide_pack : core.

Lemma bool_decide_eq_true (P : Prop) `{Decision P} : bool_decide P = true ↔ P.
Proof. case_bool_decide; intuition discriminate. Qed.
Lemma bool_decide_eq_false (P : Prop) `{Decision P} : bool_decide P = false ↔ ~P.
Proof. case_bool_decide; intuition discriminate. Qed.
Lemma bool_decide_iff (P Q : Prop) `{Decision P, Decision Q} :
  (P ↔ Q) -> bool_decide P = bool_decide Q.
Proof. repeat case_bool_decide; tauto. Qed.

Lemma bool_decide_eq_true_1 P `{!Decision P}: bool_decide P = true -> P.
Proof. apply bool_decide_eq_true. Qed.
Lemma bool_decide_eq_true_2 P `{!Decision P}: P -> bool_decide P = true.
Proof. apply bool_decide_eq_true. Qed.

Lemma bool_decide_eq_false_1 P `{!Decision P}: bool_decide P = false -> ~P.
Proof. apply bool_decide_eq_false. Qed.
Lemma bool_decide_eq_false_2 P `{!Decision P}: ~P -> bool_decide P = false.
Proof. apply bool_decide_eq_false. Qed.



(** The tactic [compute_done] solves the following kinds of goals:
- Goals [P] where [Decidable P] can be derived.
- Goals that compute to [True] or [x = x].

The goal must be a ground term for this, i.e., not contain variables (that do
not compute away). The goal is solved by using [vm_compute] and then using a
trivial proof term ([I]/[eq_refl]). *)
Tactic Notation "compute_done" :=
  try apply (bool_decide_unpack _);
  vm_compute;
  first [ exact I | exact eq_refl ].
Tactic Notation "compute_by" tactic(tac) :=
  tac; compute_done.

(** Backwards compatibility notations. *)
Notation bool_decide_true := bool_decide_eq_true_2.
Notation bool_decide_false := bool_decide_eq_false_2.


(* %%%%%%%%%%%%%%%%%%%%%%%% *)

(** * [EqbDec] is a typeclass for boolean-equality supporting types *)
 
(** If we can make a boolean equality and show [beq_eq] then we get reflection (below) *)

Class EqbDec (X: Type) := {
  beq: X -> X -> bool;
  beq_eq: forall x y, if beq x y then x = y else x <> y
}.
(* Infix "=?" := beq (at level 70). *)
(* Infix "!=" := nbeq (at level 70). *)

Definition nbeq {X} {eqa: EqbDec X} (x y: X) := negb (beq  x y).

Lemma beq_rfl {X: Type} {eqb_dec: EqbDec X} : 
  forall (x: X), beq x x = true.
Proof.
  intros x. 
  destruct (beq x x) eqn:e. easy.
    assert (a:= beq_eq x x). now rewrite e in a.
Qed.

Lemma beq_reflect {X: Type} {eqb_dec: EqbDec X} : 
  forall x y, reflect (eq x y) (beq x y).
Proof.
  intros x y.
  apply  iff_reflect.
  split.
  - intros Heq.
    subst. apply beq_rfl.
  - intros. 
    destruct (beq x y) eqn:e.     
    + assert (a:= beq_eq x y). now rewrite e in a.
    + congruence.
Qed.

(** just convenience *)
Lemma beq_eq' {X} {eqa: EqbDec X} (x y: X):
  beq x y = true -> x = y.
intros.
pose proof (beq_eq x y).
rewrite H in H0.
assumption.
Qed.

(* ------------------------------------------------------- *)
(** *** Relating EqbDec with EqDecision *)

(* ----------------------- *)
(** From EqDecision to EqbDec *)

Definition EqbDec_of_eq_dec{X} (eq_dec: forall (x y: X), {x = y} + {x <> y}): 
  EqbDec X.
apply (Build_EqbDec X (fun x y => if eq_dec x y then true else false)).
intros.
destruct (eq_dec x y); congruence.
Defined.


Global Instance eqDecisionEqbDec {X} `{EqDecision X} : EqbDec X.
Proof.
 apply ( Build_EqbDec X (fun x y => if eq_dec x y then true else false)).
 apply EqbDec_of_eq_dec.
Defined. 


(* ----------------------- *)
(** From EqbDec to EqDecision *)

Definition beq_to_eqdec {X} {eqa: EqbDec X} (x y: X): {x = y} + {x <> y}.
pose proof (beq_eq x y).
destruct (beq x y); auto.
Defined.

Global Instance eqbDecEqDecision {X} `{EqbDec X} : EqDecision X.
Proof.  intros x y. apply beq_to_eqdec.
Defined.



(** @@ Example. Since we have

Instance nat_eq_dec : EqDecision nat.

 we can do the following
*)
 #[export] Instance eqbDec_nat : EqbDec nat 
   := EqbDec_of_eq_dec nat_eq_dec.



(* --------------------- *)
(** From Bart Jacobs *)

Lemma Forall2_implies_Forall2{X Y}(P Q: X -> Y -> Prop):
  (forall x y, P x y -> Q x y) ->
  forall xs ys,
  Forall2 P xs ys ->
  Forall2 Q xs ys.
intros.
revert ys H0.
induction xs; destruct ys; intros H0; inversion H0; constructor.
- auto.
- auto.
Qed.

Lemma Forall2_map1{X1 X2 Y}(P: X2 -> Y -> Prop)(f: X1 -> X2) xs ys:
  Forall2 P (map f xs) ys <-> Forall2 (fun x y => P (f x) y) xs ys.
revert ys.
induction xs; intros; destruct ys; simpl; split; intro H1; try inversion H1; constructor; auto.
apply IHxs.
assumption.
apply IHxs.
assumption.
Qed.


Section Forall2b.

Context {X B}(p: X -> B -> bool).

Fixpoint forall2b(xs: list X)(ys: list B): bool :=
  match xs, ys with
    [], [] => true
  | x::xs, y::ys => p x y && forall2b xs ys
  | _, _ => false
  end.

End Forall2b.

Lemma forall2b_Forall2{X B}(p: X -> B -> bool)(xs: list X)(ys: list B):
  forall2b p xs ys = true ->
  Forall2 (fun x y => p x y = true) xs ys.
revert ys.
induction xs; intros; destruct ys; simpl in *; try discriminate; constructor.
- apply Bool.andb_true_iff in H.
  tauto.
- apply IHxs.
  apply Bool.andb_true_iff in H.
  tauto.
Qed.

Lemma forall2b_eqb_eq{X}{eqa: EqbDec X}(xs ys: list X):
  forall2b beq xs ys = true ->
  xs = ys.
revert ys.
induction xs as [|x xs]; destruct ys as [|y ys]; simpl; try tauto; intros; try congruence.
apply Bool.andb_true_iff in H.
destruct H.
apply beq_eq' in H.
subst.
apply IHxs in H0.
congruence.
Qed.

(** ** EqbDec for lists *)


Lemma eqb_eq_list {X: Type} {_ : EqbDec X} :
forall x y : list X, if forall2b beq x y then x = y else x ≠ y.
Proof.
induction x.
- intro y.
  destruct y.
  + reflexivity.
  + intro H.
    discriminate.
- intros y.
  destruct y as [| a0 rest].
  + intro.   discriminate.
  + simpl.
    pose proof (beq_eq a a0).
    pose proof (IHx rest).
    destruct (beq a a0).
    * destruct (forall2b beq x rest).
      -- subst. reflexivity.
      -- simpl. congruence.
    * simpl. congruence.
Defined.

#[export] Instance eqbDec_list {X} {blah : EqbDec X}: EqbDec (list X) .
Proof.
   assert (h:= Build_EqbDec (list X) (fun x y => forall2b beq x y)).
   apply h.
   assert (h1:=  eqb_eq_list).
   apply h1.
Defined.

 
(* =============================== *)
(** * Connecting sumbool with booleans *)
(* =============================== *)

Definition sumbool_to_bool :
  forall P Q : Prop, {P} + {Q} -> bool :=
  fun P Q sb => if sb then true else false.

Arguments sumbool_to_bool {P} {Q} _.

Lemma sumbool_to_bool_correct_left 
  (P Q :Prop) (sb :  {P} + {Q}) :
  (@sumbool_to_bool P Q sb) = true -> P.
Proof.  
  intros H.
  unfold sumbool_to_bool in H.
  destruct sb as [y | n]; easy.
Qed.

Lemma sumbool_to_bool_correct_right
  (P Q :Prop) (sb :  {P} + {Q}) :
  (@sumbool_to_bool P Q sb) = false -> Q.
Proof.  
  intros H.
  unfold sumbool_to_bool in H.
  destruct sb as [y | n]; easy.
Qed.

(** NB: don't expect iff in the above. 
Suppose P = Q ! 

But in the case Q is ~P we do get iff:
 *)

Definition dec_to_bool 
  (P : Prop) (sb: {P} + {~ P}) :=
  @sumbool_to_bool P (~P) sb.
Arguments dec_to_bool {P} _.

Lemma dec_to_bool_correct_true P sb :
  (@dec_to_bool P sb) = true <-> P. 
Proof.
  split.
  - unfold dec_to_bool.
    apply sumbool_to_bool_correct_left.
  - intros H.
    unfold dec_to_bool.
    apply not_false_is_true; intros H1.
    assert (H2:= sumbool_to_bool_correct_right P (~P) sb H1 ). 
    easy.
Qed.

Lemma dec_to_bool_correct_false P sb :
  (@dec_to_bool P sb) = false <-> (~ P).
Proof.
  assert (H1:= dec_to_bool_correct_true P sb).
  assert (H2:= not_true_iff_false (dec_to_bool sb)).
  firstorder.
Qed.

Scheme Equality for string.
(** 
 string_beq is defined
     : string -> string -> bool

  string_eq_dec is defined
     : forall x y : string, {x = y} + {x <> y}

internal_string_dec_bl:
  ∀ x : string, (λ x0 : string, ∀ y : string, string_beq x0 y = true → x0 = y) x

internal_string_dec_lb:
  ∀ x : string, (λ x0 : string, ∀ y : string, x0 = y → string_beq x0 y = true) x

*)

#[export] Instance string_dec :
 EqDecision string.
Proof.
  exact string_eq_dec.
Defined.



(** Help using [Scheme Equality] *)
 
(** Given a type with a boolean equality and a reflection lemma,
derive an [eqb-eq] function as required by the EqbDecision typeclass.

Note that when we get our boolean equality from the [Scheme]
mechanism, the internally derived functions make it easy to build the
[reflect] lemma.  *)
Lemma reflect_to_eqb_eq {X: Type} {X_beq : X -> X -> bool}
  (rflct :  ∀ x y : X, reflect (x = y) (X_beq x y)) :
  forall x y, if X_beq x y then x = y else x <> y.
Proof.
  intros x y; now destruct (rflct x y).
Qed.
