(* Time-stamp: <Wed 11/22/23 11:31 Dan Dougherty Sorts.v> *)

From RC Require Import 
  Utilities
  Decidability.

(** * Sorts *)
Inductive sort : Set :=
  Text                       (* Plaintext *)
| Data                       (* Data *)
| Name                       (* Name *)
| Skey                       (* Symmetric key *)
| Akey                       (* Public asymmetric key *)
| Ikey                       (* Private asymmetric key *)
| Mesg                       (* Message *)
| Chan                       (* Channel *) 
.

Definition sort_eq_dec:
  forall x y: sort, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality.
Defined.
#[global]
Hint Resolve sort_eq_dec : core.

Definition sort_eqb x y: bool :=
  if sort_eq_dec x y then
    true
  else
    false.

Lemma sort_eq_correct:
  forall x y,
    sort_eqb x y = true <-> x = y.
Proof.
  intros.
  unfold sort_eqb.
  destruct (sort_eq_dec x y); subst; easy.
  (* destruct (sort_eq_dec x y); subst; intuition. *)
Qed.

Lemma sort_eq_complete:
  forall x y,
    sort_eqb x y = false <-> x <> y.
Proof.
  intros.
  unfold sort_eqb.
  destruct (sort_eq_dec x y); subst; easy.
  (* destruct (sort_eq_dec x y); subst; intuition. *)
Qed.

(** The inverse sort *)

Definition inv_sort (x: sort): sort :=
  match x with
  | Akey => Ikey
  | Ikey => Akey
  | s => s
  end.

Definition is_asym_key_sort (s: sort) : bool :=
  match s with
  | Akey => true
  | Ikey => true
  | _ => false
  end.

(* * Showing *)

Open Scope string_scope.
#[export] Instance show_sort : Show sort := 
  {show := fun s =>
             match s with 
               Text  => "Text"       
             | Data  => "Data"       
             | Name => "Name"
             | Skey => "Skey"
             | Akey => "Akey"
             | Ikey => "Ikey"
             | Mesg => "Mesg"
             | Chan => "Chan"
             end}.
Close Scope string_scope.
