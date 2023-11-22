(* Time-stamp: <Sat 6/3/23 12:19 Dan Dougherty Show.v> *)
Require Import String List.
Import ListNotations.

From RC Require Import
  Utilities
  Decidability
  Sorts
  Term
  Proc
.

(* =============================== *)
(** * Showing *)
Open Scope string_scope.
#[export] Instance show_tloc : Show tloc :=
  {show := fun l => 
             match l with
             | L n t => "l_" ++ (show n) ++ (show t)
             end}.

#[export] Instance show_expr : Show expr := 
  {show := fun e =>
             match e with 
             | _Pair l1 l2 => "_Pair " ++ show l1 ++ show l2
             | _Encr l1 l2 => "_Encr " ++ show l1 ++ show l2
             | _Hash l => "_Hash " ++ show l
             | _Genr s => "_Hash " ++ show s
             | _Quot s => "_Quot " ++ s
             | _Read  => "_Read () " 
             | _Frst l => "_Hash " ++ show l
             | _Scnd l => "_Hash " ++ show l
             | _Decr l1 l2 => "_Hash " ++ show l1 ++ show l2
             end}.

#[export] Instance show_smt : Show smt :=
  {show := fun s =>
             match s with 
             | Snd c t => "Snd " ++ show c ++ show t
             | Rcv c t => "Rcv " ++ show c ++ show t
             | Bnd t e => "Bnd " ++ show t ++ show e
             | Inv l1 l2 => "Bnd " ++ show l1 ++ show l2
             | _Same l1 l2 => "_Same " ++ show l1 ++ show l2
             | _Csrt l s => "_Csrt " ++ show l ++ show s
             | Ret ls => "Ret " ++ show ls
             | Com s =>  "Com" ++ show s
             end}.

#[export] Instance show_tproc : Show tproc :=
  {show := fun p =>
             "tProc " 
               ++ show (inputtlocs p)
               ++ "\n"
               ++ show (outputSorts p)
               ++ show (body p)
}.


Close Scope string_scope.
