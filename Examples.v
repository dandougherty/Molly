(* Time-stamp: <Wed 11/22/23 13:10 Dan Dougherty Examples.v> *)

(** Some regrettably non-systematic testing

Some examples are adapted from a suite of protocol examples for Ramsdell's Roletran compiler.
    
A few of the examples, towards the end, take a while to complete (max
is a little over a minute).  Those computations have been
commented-out to permit running the buffer in one go.
 *)

Require Import Arith Bool List ZArith String. 
Import ListNotations.

From RC Require Import
CpdtTactics
Utilities
Decidability
ListUtil
Act
Sorts
Term
Subterms
Role
SaturationRules
SaturationLoop
Compile
Proc
roleToRole
. 

(** allow for using a [role] wherever a [Role] is expected. *)
Coercion role_to_Role : role >-> Role.


(* ============================================ *)
(** * Debugging and testing *)
(* ============================================ *)

(** compile then show the role and the proc *)

(** Since role_to_Role is a coercion we can use Roletran roles
if we like *)

Inductive Role_and_proc : Role -> (optionE Proc) -> Type :=
  RP rl pr : Role_and_proc rl pr.

Definition go (r: Role) :=
  Role_and_proc r (compile r).

(* ------------------------------------ *)



(* testing initialization *)

Definition init_pri : Role := 
         [Prm (Ch 1); 
          Snd (Ch 1) ((Ik (Av 2)))
         ].
Compute go init_pri.

Definition init_pub : Role := 
         [Prm (Ch 1); 
          Snd (Ch 1) ((Ak (Av 2)))
         ].
Compute go init_pub.

Definition init_both : Role := 
         [Prm (Ch 1); 
          Snd (Ch 1) ((Ak (Av 2)));
            Snd (Ch 1) ((Ik (Av 2)))
         ] .
Compute go init_both.

Definition init_neither : Role := 
         [Prm (Ch 1); 
          Rcv (Ch 1) ((Ak (Av 2)));
          Rcv (Ch 1) ((Ik (Av 2)));
          Rcv (Ch 1) ((Ak (Av 2)))
         ].
Compute go init_neither.

Definition empty_state : state :=
  mkState [] [] (SomeE []).
 
Definition initial_bindings_state (rl: Role) : state :=
  mkState [] rl (SomeE (initial_bindings rl)).


Definition akey_tst : Role := 
         [Prm (Ch 1); Prm (Ak (Av 2));
         Rcv (Ch 1) (Pr (Nm 0) (Ik (Av 2)));
         Snd (Ch 1) (En (Nm 0) (Ak (Av 2)))]
.
Compute go akey_tst.
 
Definition msg_role :Role :=
  [Prm (Ch 1);
  Snd (Ch 1) (Mg 1) ;
  Snd (Ch 1) (Mg 2) ;
  Rcv (Ch 1) (Mg 2) 
] .

Compute go msg_role.

Definition talk_eg :=
  [          (Prm (Ch 1)) ; 
             Prm (Dt 1); 
             Snd((Ch 1))((Nm 1)); 
             Rcv((Ch 1))(Pr((Nm 1))((Dt 1))); 
             Snd((Ch 1))(En((Nm 1))((Dt 1))); 
             Rcv((Ch 1))(En((Nm 1))((Dt 1)))  ]
.
Compute go talk_eg.



Definition r1_hash :Role :=
  [Prm (Ch 1);
  Snd (Ch 1) (Hs (Dt 1)) ] .

Compute go r1_hash.

Definition r2_hash_bad :Role :=
  [Prm (Ch 1); 
  Rcv (Ch 1) (Hs (Dt 1)) ] .

Compute go r2_hash_bad.

Definition r3_hash :Role :=
  [Prm (Ch 1); Prm (Dt 1);
  Rcv (Ch 1) (Hs (Dt 1)) ] .

Compute go r3_hash .



Definition r_quote : Role := 
  [Prm (Ch 1); 
  Rcv (Ch 1) (Qt "bye") ]  .
Compute go r_quote.
Compute (Subterms_of_role r_quote) .

Definition rnil :=
  {|
    inputs := [];
    trace := [];
    uniqs := [];
    outputs :=  []
  |}. 

 
Compute go rnil. 

Definition r0 :=
  {|
    inputs := [Ch 1; Tx 2];
    trace := [];
    uniqs := [];
    outputs :=  [Tx 2]
  |}.


Compute go r0.

Definition r1 :=
  {|
    inputs := [Ch 1];
    trace := [Rv 1 (Tx 1);   Rv 1 (Tx 2)];

    uniqs := [];
    outputs :=  []
  |}. 
Compute go r1. 

Definition rrepeats :=
  {|
    inputs := [Ch 1];
    trace := [Rv 1 (Tx 1);   
              Rv 1 (Tx 1);
              Sd 1 (Tx 1);
              Rv 1 (Tx 1);
              Sd 1 (Tx 1)];

    uniqs := [];
    outputs :=  []
  |}.  
Compute go rrepeats. 


Definition r11 :=
  {|
    inputs := [Ch 1; Tx 1];
    trace := [Rv 1 (Tx 1)];
    uniqs := [];
    outputs :=  []
  |}.
Definition R11 := role_to_Role r11.
Compute go r11.

Definition Blanchet_init_role: role :=
  mkRole
  [Sd 2 (En (En (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0))) (Ak (Pb 1)));
   Rv 2 (En (Dt 3) (Sk (Sv 4)))]
  [Sk (Sv 4)]
  [Ch 2; Nm 1; Ik (Pb 0); Ak (Pb 1)]
  [Dt 3; Sk (Sv 4)].

Compute go Blanchet_init_role.
 

(* ==================================================== *)


Definition for_paper := 
  [Prm (Ch 1); 
   Prm (Dt 1); 
   Snd (Ch 1) (Pr (Dt 1) (Dt 2)) ;
   Snd (Ch 1) (Dt 2) ;
   Ret (Dt 2) ]
.

Compute go for_paper. 

Definition  kypr_eg :=
  mkRole
  [Sd 2 (En (En (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0))) (Ak (Pb 1)));
   Rv 2 (En (Dt 3) (Sk (Sv 4)))]
  [Sk (Sv 4)]
  [Ch 2; Nm 1; Ik (Pb 0); Ak (Pb 1)]
  [Dt 3; Sk (Sv 4)].

Compute role_to_Role kypr_eg.

Definition kyprgo :=
  [Prm (Ch 2); 
   Prm (Ik (Pb 1));
   Prm (Ak (Pb 1));
   Prm (Ik (Av 2));
   Prm (Ak (Av 2))

]
    : Role.

Compute go kyprgo.

Definition togo:= 
            [
            Bind (Ch 2, L 1) (Param 1);
            Bind (Ik (Pb 1), L 2) (Param 2);
            Bind (Ak (Pb 1), L 3) (Param 3);

            Bind (Ik (Av 2), L 4) (Param 2);
            Bind (Ak (Av 2), L 5) (Param 3)
            ].

Definition rho_role: role :=
  mkRole
  [Rv 1 (Pr (Nm 0) (Ik (Av 2))); Sd 1 (En (Nm 0) (Ak (Av 2)))]
  []
  [Ch 1; Ak (Av 2)]
  [].

Definition rho_Role := 
         [Prm (Ch 1); Prm (Ak (Av 2));
         Rcv (Ch 1) (Pr (Nm 0) (Ik (Av 2)));
         Snd (Ch 1) (En (Nm 0) (Ak (Av 2)))]
.

Compute go rho_Role.

Definition r2 :=
  {|
    inputs := [Ch 1; Nm 1];

    trace := [
      Sd  1  (Dt 1) ;
       Rv  1  (Dt 17);
       Sd  1  (Dt 18);
       Rv  1  (Dt 17)
    ];
    
    uniqs := []; 
    outputs :=  [] 
|}. 
Compute go r2.


(* Compute gir r2. *)

Compute role_to_Role r2.

Check role_to_Role.

Definition reqs:=
  {|
    inputs := [Ch 1];

    trace := [
      Rv  1 (Dt 17);
      Rv  1 (Dt 99) ;
      Sd 1 (Dt 17)
    ];
    
    uniqs := [];
    outputs :=  []
  |}.

Compute go reqs.

Definition r_same_check :=
  {|
    inputs := [Ch 1 ];

    trace := [
       Rv  1 (Pr (Dt 17) (Dt 17))
         ; Rv  1 (Pr (Dt 17) (Dt 16))
    ];
    
    uniqs := []; 
    outputs :=  [] 
|}. 
 

Compute go r_same_check.


Definition rwi: role :=
  {|
    inputs := [Ch 1; Nm 1];

    trace := [
      Sd  1  (Pr (Dt 17) (Dt 17))
      ; Rv 1  (Pr (Nm 1) (Tx 3))
      ; Sd  (1) (Pr (Dt 17) (Dt 23))
    ];
    
    uniqs := [];
    outputs :=  [Pr (Dt 17) (Dt 23)]
|}.

Compute go rwi.   


Definition nochan: role :=
  {|
    inputs := [];

    trace := [
      Rv ( 99) (Ch 1); 
      Rv ( 99) (Nm 1);
      Sd  1  (Pr (Dt 17) (Dt 17))
    ];
    
    uniqs := [];
    outputs :=  []
|}.
Compute go nochan.   

Definition r3: role :=
  {|
    inputs := [Ch 1];
    trace := 
      [
        Sd 1  (Tx 1)
        ; Sd 1  (Tx 1)
        ; Rv 1  (Pr  (Tx 1) (Tx 1))
      ];
    uniqs := [];
    outputs := []
|}. 

Compute  r3.
Compute go r3.


Definition r4: role :=
  {|
    inputs :=  [Ch 1; Dt 1];
    trace := [Sd 1  (Dt 1)] ;
    uniqs := [] ;
    outputs :=   [Dt 1]
  |}.
Compute  r4. 
Compute go r4. 

(** a good series of examples, for Generate and decryption *)

Definition bad5: role := 
  {|
    inputs :=  [Ch 1; (Dt 1)];
    uniqs := [] ;
    trace := [Rv 1  (En (Dt 1) (Dt 2) ) ; 
              Sd 1  (Pr (Dt 1) (Dt 1) ) ];
    outputs :=   [(Tx 17) ; (Dt 2)]
  |}.
Compute go bad5.

Definition ok5: role := 
  {|
    inputs :=  [Ch 1; (Dt 2)];
    uniqs := [] ;
    trace := [Rv 1  (En (Dt 1) (Dt 2) ) ; 
              Sd 1  (Pr (Dt 1) (Dt 2) ) ];
    outputs :=   [(Tx 17)]
  |}.
Compute go ok5.
 
Definition maybeno5: role := 
  {|
    inputs :=  [Ch 1 ];
    uniqs := [] ;
    trace := [Rv 1  (En (Dt 1) (Dt 2) ) ; 
              Sd 1  (Dt 2) ];
    outputs :=   [(Tx 17)]
  |}.
Compute go maybeno5.

Definition maybeyes5: role := 
  {|
    inputs :=  [Ch 1 ];
    uniqs := [] ;
    trace := [
      Sd 1  (Dt 2) ;
      Rv 1  (En (Dt 1) (Dt 2) ) 
    ];
    outputs :=   [(Tx 17)]
  |}.
Compute go maybeyes5.

(* decryption key part of pair *)
Definition r55: role := 
  {|
    inputs :=  [Ch 1; (Dt 1)];
    uniqs := [] ;
    trace := [Rv 1  (Pr (En (Dt 1) (Dt 2))
                     (Dt 2) ); 
              Sd 1  (Pr (Dt 1) (Dt 1) ) ];
    outputs :=   [(Tx 17) ; (Dt 2)]
  |}.
Compute go r55.



Definition r6: role := 
  {|
    inputs :=  [Ch 1; Ch 2; Dt 1];
    trace := [Sd 1  (Pr (Dt 1) (Dt 2) ) ; 
              Rv 1  (Dt 17)
              ; Rv 1  (Dt 17)
              ; Sd ( 2) (Pr (Dt 17) (Dt 1) )
    ];
    uniqs := [] ;
    outputs :=   []
  |}.
Compute go r6.

(** testing for
- synth in the sends
- analyze in the recv, incl chck sort and check same
*)

Definition r7: role := 
  {|
    inputs :=  [Ch 1; Dt 1; Dt 2];
    uniqs := [] ;
    trace := [Sd 1  (Pr (Dt 1) (Dt 2) ) ; 
              Rv 1  (Pr (Dt 17) (Dt 1));
              Sd 1  (Pr (Dt 17) (Dt 1) ) ];
    outputs :=   []
  |}.

Compute go r7.

Definition r8: role := 
  {|
    inputs :=  [Ch 1; Dt 1; Sk (Sv 2)];
    uniqs := [] ;
    trace := [ Rv 1  (En (Dt 17) (Sk (Sv 2)));
              Sd 1  (Dt 17) ];
    outputs :=   []
  |}.
 Compute go r8.


Definition r9: role := 
  {|
    inputs :=  [Ch 1; Dt 1];
    trace := [ Rv 1  (Pr (Dt 1) (Dt 2)) ;
               Rv 1  (Pr (Dt 1) (Dt 3)) ;
               Sd 1  (Pr (Dt 2) (Dt 3)) ;
              Sd 1  (Dt 17) ];
    uniqs := [] ;
    outputs :=   []
  |}.
Compute go r9.
 

(** ** Tricky ones to test design decisions *)

(** sending hash *) 
Definition send_hash1: role :=
  {|
    inputs :=  [Ch 1; Tx 1] ;
    uniqs := [];
    trace := [
      (* Rv 1  ((Tx 1)) ;  *)
      Sd 1  (Hs (Tx 1))
];
    outputs := [(Tx 1)]
  |}. 
 
Compute go send_hash1.

Definition send_hash2: role :=
  {|
    inputs :=  [Ch 1] ;
    uniqs := [];
    trace := [
      Rv 1  ((Tx 1)) ;
      Sd 1  (Hs (Tx 1))
];
    outputs := [(Tx 1)]
  |}. 
 
Compute go send_hash2.

Definition send_hash3: role :=
  {|
    inputs :=  [Ch 1] ;
    uniqs := [];
    trace := [
      Sd 1  ((Tx 1)) ;
      Sd 1  (Hs (Tx 1))
];
    outputs := [(Tx 1)]
  |}. 
 
Compute go send_hash3.

(** receive hash; do have inside value *)
Definition receive_hash_ok: role := 
  {|
    inputs :=  [Ch 1; Tx 1] ;
    uniqs := [];
    trace := [Rv 1  (Hs (Tx 1))];
    outputs := []
  |}.

Compute go receive_hash_ok.

(* should be NoneE *)
(** receive hash but don't have inside value *)
Definition no_hash_bad: role := 
  {|
    inputs :=  [Ch 1; Tx 1] ;
    uniqs := [];
    trace := [Rv 1  (Hs (Tx 2))];
    outputs := []
  |}.

Compute go no_hash_bad.

 

(** random value needed as decryption key.  Boo.*)
Definition no_random_decrypt: role :=  
  {|
    inputs :=  [Ch 1; Tx 1] ;
    uniqs := [];
    trace := [Rv 1  (En (Tx 1) (Tx 2))];
    outputs := [Tx 2]
  |}.
Compute go no_random_decrypt.


(** symm encryption needed as decryption key, even though generable.  Boo *)
Definition no_ei_decrypt :=
  {|
    inputs :=  [Ch 1; Dt 1; Dt 2];
    trace := [Rv 1  (En (Dt 3) (En (Dt 1) (Dt 2)))];
    outputs := [Dt 3];
    uniqs := []
  |}. 
Compute go no_ei_decrypt. 

(** symm encryption needed as decryption key, even though generable.
Boo or ok?   Currently we allow this.  *)
Definition lax_decrypt :=
  {|
    inputs :=  [Ch 1; Dt 1; Dt 2];
    trace := [Rv 1  (En (Dt 3) (En (Dt 1) (Dt 2)))];
    outputs := [Dt 3];
    uniqs := []
  |}.

Compute go lax_decrypt.
 

Definition bli2: role :=
  mkRole
  [Rv 2 (Pr (Pr (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0))) (Ak (Pb 1)));
   Sd 2 (Pr (Dt 3) (Sk (Sv 4)))]
  [Dt 3]
  [Ch 2; Nm 1; Ak (Pb 0); Ik (Pb 1)]
   [Dt 3; Sk (Sv 4)].

Compute go bli2.
 
Definition blr4: role :=
  mkRole
  [Rv 2 (En (En (Pr (Ak (Av 1)) (Sk (Sv 4))) (Ik (Av 0))) (Ak (Av 1)));
   Sd 2 (En (Dt 3) (Sk (Sv 4)))]
  [Dt 3]
  [Ch 2; Ak (Av 0); Ik (Av 1)]
  [Dt 3; Sk (Sv 4)].
 
 Compute go blr4.

Definition Blanchet_init := 
  [Prm (Ch 2); Prm (Nm 1); Prm (Ik (Pb 0));
   Prm (Ak (Pb 1));
   Snd (Ch 2)
     (En
        (En (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0)))
        (Ak (Pb 1)));
   Rcv (Ch 2) (En (Dt 3) (Sk (Sv 4)));
   Ret (Dt 3); Ret (Sk (Sv 4))]
     : Role .
 
Compute go Blanchet_init.

Definition  bli1 :=
  [Prm (Ch 2); 
   Prm (Nm 1); 
   Prm (Ik (Pb 0));
   Prm (Ak (Pb 1));
   Snd (Ch 2) (En (En (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0))) (Ak (Pb 1)));
   Rcv (Ch 2) (En (Dt 3) (Sk (Sv 4))); 
   Ret (Dt 3);
   Ret (Sk (Sv 4))]
.

Compute go bli1.

Definition blah1 :=
  [Prm (Ch 2); Prm (Nm 1)
   ; Rcv (Ch 2) (En
                 (Pr (Nm 1) (Nm 1) )
                 (Nm 1)
                 )
  ]
    : Role.


Compute go blah1.

Definition blah2 :=
  [Prm (Ch 2); Prm (Nm 1)
   ; Rcv (Ch 2) (Pr
                 (Pr (Nm 1) (Tx 1) )
                 (Dt 1)
                 )
  ].
 
Compute go blah2 .


Definition blr3 :=
  [Prm (Ch 2); Prm (Nm 1); 
   Prm (Ak (Pb 0));
   Prm (Ik (Pb 1)); 
   Rcv (Ch 2) (Tx 23);
   Snd (Ch 2)
     (Pr (Pr (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0)))
        (Ak (Pb 1)));
   Snd (Ch 2) (Pr (Dt 3) (Sk (Sv 4)));
   Ret (Dt 3); Ret (Sk (Sv 4))]
    : Role.

Compute go blr3.

Definition bli3: role :=
  mkRole
  [Sd 2 (En (En (Pr (Ak (Av 1)) (Sk (Sv 4))) (Ik (Av 0))) (Ak (Av 1)));
   Rv 2 (En (Dt 3) (Sk (Sv 4)))]
  [Sk (Sv 4)]
  [Ch 2; Ak (Av 1); Ik (Av 0)]
  [Dt 3; Sk (Sv 4)].

Compute go bli3.

Definition blr1: role :=
  mkRole
  [ Rv 2 (Tx 23);
    Sd 2 (Pr (Pr (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0))) (Ak (Pb 1)));
   Sd 2 (Pr (Dt 3) (Sk (Sv 4)))]
  [Dt 3]
  [Ch 2; Nm 1; Ak (Pb 0); Ik (Pb 1)]
   [Dt 3; Sk (Sv 4)].

Compute go blr1.


Definition owi: role :=
  {|
    inputs := [Ch 4; Nm 0; Nm 1; Sk (Lt 0 5)];

    trace := [Sd ( 4) (Pr (Nm 0) (Pr (Nm 1) (Tx 3)));
              Rv ( 4) (En (Pr (Tx 3) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
                           (Sk (Lt 0 5)))];
    
    uniqs := [Tx 3];
    outputs :=  [Sk (Sv 2)]
|}.
 
Compute go owi.

Definition owr: role :=
  {|
    inputs := [Ch 6; Ch 7; Nm 1; Sk (Lt 1 8)];
    trace := 
      [Rv ( 6) (Pr (Nm 0) (Pr (Nm 1) (Tx 3)));
       Sd ( 7) (Pr (Nm 0) 
                    (Pr (Nm 1) (Pr (Tx 3) (Tx 4))));
       Rv ( 7) (Pr (Mg 5)
                    (En (Pr (Tx 4) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
                       (Sk (Lt 1 8))));
       Sd ( 6) (Mg 5)];
    uniqs := [Tx 4];
    outputs := [Nm 0; Sk (Sv 2)]
|}.

(* Compute go owr. *)


(* ============================================ *)
(** Role: rho (privk.scm:4:3) *)

Definition privk: Role :=
        [Prm (Ch 1); Prm (Ak (Av 2));
          Rcv (Ch 1) (Pr (Nm 0) (Ik (Av 2)));
          Snd (Ch 1) (En (Nm 0) (Ak (Av 2)))] .

Compute go privk.

(* ============================================ *)

(** Role: rho (pubk.scm:4:3) *)

Definition pubk := 
  [Prm (Ch 1); Prm (Ik (Av 2));
   Rcv (Ch 1) (En (Pr (Nm 0) (Ak (Pb 0))) (Ak (Av 2)));
        Snd (Ch 1) (En (Nm 0) (Ak (Pb 0)))]
    : Role.

Compute compile pubk.

(* ============================================ *)

(** Role: rho (pubk2.scm:4:3) *)

Definition pubk2 :=
  [Prm (Ch 1); Prm (Ik (Av 2));
        Rcv (Ch 1) (En (Pr (Nm 0) (Ak (Pb 0))) (Ak (Av 2)));
        Snd (Ch 1) (En (Nm 0) (Ak (Pb 0)))]
     : Role .

Compute compile pubk2.

(* ============================================ *)


(** Role: init (bad_unilateral.scm:7:3) *)
(* ------------------------------------*)
 
Definition bad_unilateral_init := 
  [Prm (Ch 0); Prm (Ak (Av 1)); Snd (Ch 0) (En (Tx 2) (Ak (Av 1)));
   Rcv (Ch 0) (Tx 2); Ret (Tx 2)]
    : Role.

Compute compile bad_unilateral_init.

(* ============================================ *)
(** Role: resp (bad_unilateral.scm:15:3) *)

Definition bad_unilateral_resp
     := [Prm (Ch 0); Prm (Ak (Av 1)); Rcv (Ch 0) (En (Tx 2) (Ik (Av 1)));
        Snd (Ch 0) (Tx 2); Ret (Tx 2)]
     : Role .

Compute compile bad_unilateral_resp.
          
(** Role: init (unilateral_invk.scm:10:3) *)


Definition unilateral_init :=
 [Prm (Ch 0); 
  Prm (Ak (Av 1)); 
  Snd (Ch 0) (En (Tx 2) (Ak (Av 1)));
  Rcv (Ch 0) (Tx 2); Ret (Tx 2)]
.

Compute compile unilateral_init.

(* ============================================ *)

(** Role: resp (unilateral_invk.scm:18:3) *)

Definition unilateral_resp :=
 [Prm (Ch 0); Prm (Ak (Av 1)); Rcv (Ch 0) (En (Tx 2) (Ik (Av 1)));
        Snd (Ch 0) (Tx 2); Ret (Tx 2)]
     : Role .

Compute compile unilateral_resp.

(* ============================================ *)

(* Role: rho (invk.scm:4:3) *)

Definition invk := 
  [Prm (Ch 1); Prm (Ak (Av 2)); Rcv (Ch 1) (Pr (Nm 0) (Ik (Av 2)));
   Snd (Ch 1) (En (Nm 0) (Ak (Av 2)))]
    : Role .

Compute compile invk.
          
(* ============================================ *)


(* Role: rho (ltk.scm:4:3) *)


Definition ltk : Role :=
         [Prm (Ch 2); Prm (Ik (Av 3));
          Rcv (Ch 2)
            (En (Pr (Nm 0) (Pr (Nm 1) (Sk (Lt 0 1)))) (Ak (Av 3)));
          Snd (Ch 2) (En (Pr (Nm 0) (Nm 1)) (Sk (Lt 0 1)))].

Compute compile ltk.

(* ============================================ *)

(* Role: init (nsl.scm:4:3) *)

Definition nsl_init :=
     [Prm (Ch 2); 
      Prm (Ik (Av 0)); 
      Prm (Ak (Av 0));
      Prm (Ak (Av 1));
      Snd (Ch 2) (En (Pr (Tx 3) (Ak (Av 0))) (Ak (Av 1)));
      Rcv (Ch 2) (En (Pr (Tx 3) (Pr (Tx 4) (Ak (Av 1)))) (Ak (Av 0)));
      Snd (Ch 2) (En (Tx 4) (Ak (Av 1)));
      Ret (Tx 3);
      Ret (Tx 4)]
    : Role .

Compute compile nsl_init.

(* ============================================ *)

(** Role: resp (nsl.scm:13:3) *)

Definition nsl_resp
     := [Prm (Ch 2); Prm (Ik (Av 1)); Prm (Ak (Av 1));
        Prm (Ak (Av 0));
        Rcv (Ch 2) (En (Pr (Tx 3) (Ak (Av 0))) (Ak (Av 1)));
        Snd (Ch 2) (En (Pr (Tx 3) (Pr (Tx 4) (Ak (Av 1)))) (Ak (Av 0)));
        Rcv (Ch 2) (En (Tx 4) (Ak (Av 1))); Ret (Tx 4);
        Ret (Tx 3)]
     : Role .

Compute compile nsl_resp.

(* ============================================ *)

(** Role: init (otway_rees.scm:9:3) *)

Definition otway_rees_init :=
  [Prm (Ch 4); Prm (Nm 0); Prm (Nm 1); Prm (Sk (Lt 0 5));
   Snd (Ch 4) (Pr (Nm 0) (Pr (Nm 1) (Tx 3)));
   Rcv (Ch 4)
     (En (Pr (Tx 3) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
        (Sk (Lt 0 5))); Ret (Sk (Sv 2))].

Compute go otway_rees_init.
    

(* ============================================ *)

(** Role: resp (otway_rees.scm:20:3) *)

Definition otway_rees_resp: Role :=
  [Prm (Ch 6); Prm (Ch 7); Prm (Nm 1); Prm (Sk (Lt 1 8));
   Rcv (Ch 6) (Pr (Nm 0) (Pr (Nm 1) (Tx 3)));
   Snd (Ch 7) (Pr (Nm 0) (Pr (Nm 1) (Pr (Tx 3) (Tx 4))));
   Rcv (Ch 7)
     (Pr (Mg 5)
        (En (Pr (Tx 4) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
           (Sk (Lt 1 8)))); Snd (Ch 6) (Mg 5);
   Ret (Nm 0); Ret (Sk (Sv 2))].

(* slow: 7 sec *)
Compute go otway_rees_resp.


(* ============================================ *)

(** Role: serv (otway_rees.scm:34:3) *)

Definition otway_rees_serv: Role :=
  [Prm (Ch 5); Prm (Nm 0); Prm (Nm 1); Prm (Sk (Lt 0 6));
   Prm (Sk (Lt 1 6));
   Rcv (Ch 5) (Pr (Nm 0) (Pr (Nm 1) (Pr (Tx 3) (Tx 4))));
   Snd (Ch 5)
     (Pr
        (En (Pr (Tx 3) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
           (Sk (Lt 0 6)))
        (En (Pr (Tx 4) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
           (Sk (Lt 1 6)))); Ret (Sk (Sv 2))] .

(* slow 6 sec *)
Compute go otway_rees_serv.



(* ============================================ *)

(** Role: init (yahalom.scm:9:3) *)

Definition yahalom_init:=
 [Prm (Ch 6); Prm (Ch 7); Prm (Nm 0); Prm (Nm 1);
        Prm (Sk (Lt 0 8)); Snd (Ch 6) (Pr (Nm 0) (Tx 3));
        Rcv (Ch 7)
          (Pr
             (En (Pr (Nm 1) (Pr (Sk (Sv 2)) (Pr (Tx 3) (Tx 4))))
                (Sk (Lt 0 8))) (Mg 5));
        Snd (Ch 6) (Pr (Mg 5) (En (Tx 4) (Sk (Sv 2))));
        Ret (Sk (Sv 2))]
     : Role .

Compute compile yahalom_init.

(* ============================================ *)

(** Role: resp (yahalom.scm:23:3) *)

Definition yahalom_resp :=
[Prm (Ch 5); Prm (Ch 6); Prm (Nm 1); Prm (Sk (Lt 1 7));
        Rcv (Ch 5) (Pr (Nm 0) (Tx 3));
        Snd (Ch 6)
          (Pr (Nm 1) (En (Pr (Nm 0) (Pr (Tx 3) (Tx 4))) (Sk (Lt 1 7))));
        Rcv (Ch 5)
          (Pr (En (Pr (Nm 0) (Sk (Sv 2))) (Sk (Lt 1 7)))
             (En (Tx 4) (Sk (Sv 2)))); Ret (Nm 0);
        Ret (Sk (Sv 2))]
     : Role .

Compute yahalom_resp.

(* ============================================ *)

(** Role: serv-init (yahalom.scm:36:3) *)

Definition yahalom_serv_init := 
  [Prm (Ch 4); Prm (Nm 1); Prm (Sk (Lt 1 5));
   Rcv (Ch 4)
     (Pr (Nm 1) (En (Pr (Nm 0) (Pr (Tx 2) (Tx 3))) (Sk (Lt 1 5))));
   Ret (Nm 0); Ret (Tx 2); Ret (Tx 3)]
    : Role .

Compute compile yahalom_serv_init.

(* ============================================ *)

(** Role: serv-complete (yahalom.scm:45:3) *)

Definition yahalom_serv_complete :=
  [Prm (Ch 5); Prm (Nm 0); Prm (Nm 1); Prm (Sk (Lt 0 6));
   Prm (Sk (Lt 1 6)); Prm (Tx 3); Prm (Tx 4);
   Snd (Ch 5)
     (Pr
        (En (Pr (Nm 1) (Pr (Sk (Sv 2)) (Pr (Tx 3) (Tx 4))))
           (Sk (Lt 0 6)))
        (En (Pr (Nm 0) (Sk (Sv 2))) (Sk (Lt 1 6))));
   Ret (Sk (Sv 2))]
    : Role .

Compute compile  yahalom_serv_complete.


(* ============================================ *)

(** Role: com-login (wp.scm:23:3) *)

Definition com_login: Role :=
  [Prm (Ch 2); Prm (Ch 3); Prm (Ch 4); Prm (Nm 1);
   Prm (Nm 8); Prm (Sk (Sv 7)); Rcv (Ch 3) (Tx 6);
   Snd (Ch 4)
     (Pr (Nm 1)
        (Pr (Tx 5)
           (Hs (Pr (Nm 8) (Pr (Tx 5) (Pr (Tx 6) (Sk (Sv 7))))))));
   Rcv (Ch 3)
     (Pr (Nm 8) (Pr (Hs (Pr (Tx 5) (Sk (Sv 7)))) (Mg 0)));
          Snd (Ch 2)
            (Pr (Qt "c-auth-blob")
               (Pr (Nm 1) (Pr (Nm 8) (Pr (Tx 5) (Mg 0)))));
          Ret (Tx 5); Ret (Mg 0)] .

(* slow 13 sec *)
(* Compute go com_login. *)


(* ============================================ *)

(** Role: wp-login (wp.scm:42:3) *)

Definition wp_login: Role :=
         [Prm (Ch 3); Prm (Ch 1); Prm (Ch 2); Prm (Nm 8);
          Prm (Nm 0); Prm (Sk (Sv 7)); Prm (Tx 4);
          Snd (Ch 1) (Tx 6);
          Rcv (Ch 2)
            (Pr (Nm 0)
               (Pr (Tx 5)
                  (Hs (Pr (Nm 8) (Pr (Tx 5) (Pr (Tx 6) (Sk (Sv 7))))))));
          Snd (Ch 1)
            (Pr (Nm 8)
               (Pr (Hs (Pr (Tx 5) (Sk (Sv 7))))
                  (Hs (Pr (Nm 0) (Pr (Tx 6) (Tx 4))))));
          Snd (Ch 3)
            (Pr (Qt "w-auth-blob")
               (Pr (Nm 8) (Pr (Nm 0) (Pr (Tx 5) (Pr (Tx 6) (Tx 4))))));
          Ret (Tx 5); Ret (Hs (Pr (Nm 0) (Pr (Tx 6) (Tx 4))))] .

(* slow 26 sec *)
(* Compute go wp_login. *)


(* ============================================ *)

(** Role: com-issue-command (wp.scm:61:3) *)


Definition com_issue_command : Role :=
      [Prm (Ch 2); Prm (Ch 6); Prm (Tx 3);
        Rcv (Ch 2)
          (Pr (Qt "c-auth-blob")
             (Pr (Nm 1) (Pr (Nm 8) (Pr (Tx 5) (Mg 0)))));
        Rcv (Ch 6)
          (Pr (Tx 9)
             (Hs
                (Pr (Qt "cm-invite") (Pr (Tx 9) (Hs (Pr (Tx 5) (Mg 0)))))));
        Snd (Ch 6)
          (Pr (Tx 4)
             (Pr (Tx 3)
                (Hs
                   (Pr (Qt "cm-deliver")
                      (Pr (Tx 9)
                         (Pr (Tx 4) (Pr (Tx 3) (Hs (Pr (Tx 5) (Mg 0))))))))));
        Rcv (Ch 6)
          (Pr (Tx 7)
             (Hs
                (Pr (Qt "cm-confirm")
                   (Pr (Tx 4)
                      (Pr (Tx 3) (Pr (Tx 7) (Hs (Pr (Tx 5) (Mg 0)))))))));
        Ret (Tx 7)] .

(* slow 45 sec  *)
(* Compute compile com_issue_command. *)

(* ============================================ *)

(** Role: wp-recv-command (wp.scm:77:3) *)

Definition wp_recv_command: Role :=
  [Prm (Ch 1); Prm (Ch 7); Prm (Tx 8);
   Rcv (Ch 1)
     (Pr (Qt "w-auth-blob")
        (Pr (Nm 9) (Pr (Nm 0) (Pr (Tx 5) (Pr (Tx 6) (Tx 4))))));
   Snd (Ch 7)
     (Pr (Tx 10)
        (Hs
           (Pr (Qt "cm-invite")
              (Pr (Tx 10)
                 (Hs
                    (Pr (Tx 5) (Hs (Pr (Nm 0) (Pr (Tx 6) (Tx 4))))))))));
   Rcv (Ch 7)
     (Pr (Tx 3)
        (Pr (Tx 2)
           (Hs
              (Pr (Qt "cm-deliver")
                 (Pr (Tx 10)
                    (Pr (Tx 3)
                       (Pr (Tx 2)
                          (Hs
                             (Pr (Tx 5)
                                (Hs (Pr (Nm 0) (Pr (Tx 6) (Tx 4)))))))))))));
   Snd (Ch 7)
     (Pr (Tx 8)
        (Hs
           (Pr (Qt "cm-confirm")
              (Pr (Tx 3)
                 (Pr (Tx 2)
                    (Pr (Tx 8)
                       (Hs
                          (Pr (Tx 5)
                             (Hs (Pr (Nm 0) (Pr (Tx 6) (Tx 4))))))))))))] .

(* slow 77 sec *)
(* Compute compile wp_recv_command. *)

