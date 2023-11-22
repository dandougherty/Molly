(** Protocol Roles from RoleTran.

RoleTran is copyright (c) 2021 The MITRE Corporation

In this file we 

- recapitulate the definition of role from module Role of Roletran.
  The type [role] is defied there.

- write a conversion [role_to_Role] from these roles to our Roles

*)

Require Import List   .
Import ListNotations.

From RC Require Import Act Term Role.

(** Make alg a synonym for Term *)
Definition alg := Term.

(* ----------------------------- *)
(** This is from Roletran *)
Inductive evt : Set :=
    Sd : nat -> alg -> evt | Rv : nat -> alg -> evt.

Record role: Set :=
  mkRole {
      trace: list evt;
      uniqs: list alg;
      inputs: list alg;
      outputs: list alg }.


(** The conversion code *)

Definition actions_from_inputs (ts : Terms) : list (Act Term) :=
 map (fun t => Prm t) ts.

Definition actions_from_outputs (ts : Terms) : list (Act Term) :=
  map (fun t => Ret t) ts.

Definition role_evt_to_act_term (ev: evt) : Act Term :=
  match ev with
    | Sd n a => Snd (Term.Ch n) a
    | Rv n a => Rcv (Term.Ch n) a
  end.

(** Note the the [uniqs] field in [role] is ignored here *)
Definition role_to_Role (r : role) : Role :=
  actions_from_inputs (inputs r) ++
    map role_evt_to_act_term (trace r) ++
    actions_from_outputs (outputs r) 
.
