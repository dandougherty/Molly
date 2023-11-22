(* Time-stamp: <Wed 11/22/23 11:03 Dan Dougherty Compile.v> 
 *)

From Coq Require Import 
  String 
  List 
  Classical_Prop
  Arith.Arith
  Bool.Bool
  Strings.String
  Logic.FunctionalExtensionality
  Lia
.
Import ListNotations.

From Equations Require Export Equations.

From RC Require Import 
  CpdtTactics TacticsMatch
  Utilities
  Decidability
  ListUtil
  Iteration
  Act
  Sorts
  Term
  Role
  Proc
  SaturationRules
  SaturationLoop
  roleToRole.


Unset Implicit Arguments. 

Section Compiling.
  (** The role is fixed throughout the compilation, so make a
  Section-global variable *)
  
  Variable rl : Role.

  Let unv := (Subterms_of_role rl).

  (** * States *)
  (* --------- *)

  (** Think of the role as cleaved into tr_done and tr_todo
by a cursor *) 
  Record state : Type :=
    mkState {
        tr_done: list (Act Term);
        tr_todo: list (Act Term);
        the_pr: optionE Proc ;
      }.

  #[export] Instance eqDecision_state : EqDecision state.
  Proof.
    intros x y.  
    solve_decision.  
    apply eqDecision_optionE.
    apply eqDecision_acts.
    apply _.
    apply eqDecision_acts.
    apply _.
  Defined.


  Definition measure (st : state) : nat := 
    length (tr_todo st).
  Arguments measure /.

  (** ** Invariants *)
  (* ------------------------- *)
  
  (** tr_done and tr_todo partition the act_trace of rl *)

  Definition cursor 
    (st: state) : Prop
    := ((tr_done st) ++ (tr_todo st)) = rl.
  (* *)
  #[export] Instance cursor_dec : 
    forall (st: state),
      (Decision (cursor st)).
  Proof. intros st.
         unfold cursor; solve_decision.
         apply eqDecision_act.
         apply _. 
  Defined.

  (** Lift into optionE *)


  (** The tr_done events line up with the prtrace of pr, via the
   cstore, ie the relation tdecl_bound *) 

  Definition done_related (st: state) : Prop
    := match (the_pr st) with
         NoneE _ => True
       | SomeE pr =>
           List_mapR (Act_mapR (tdecl_bound pr) )
             (tr_done st)
             (prtrace pr) 
       end.
  Arguments done_related /.
  (* *)
  #[export] Instance done_related_dec :
    forall (st: state), Decision (done_related st).
  Proof.
    unfold Decision.
    intros st.
    unfold done_related.
    destruct (the_pr st) eqn:e.
    - apply List_mapR_dec.    apply _.
    - apply True_dec.
  Defined.


  Definition state_saturated (st: state) : Prop :=
    match (the_pr st) with
      NoneE _ => True
    | SomeE pr =>
        (saturated_pr unv pr)
    end.
  (* *)
  #[export] Instance state_saturated_dec : 
    forall (st: state),
      (Decision (state_saturated st)).
  Proof.
    intros st.
    unfold state_saturated .
    destruct (the_pr st) eqn:e.
    - apply _ . 
    - apply True_dec.
  Defined.


  (** *)

  Definition invariant (st: state) :=  
    (state_saturated st
     /\ cursor st
     /\ done_related  st).
  (* *)
  #[export] Instance invariant_dec : 
    forall (st: state),
      (Decision (invariant st)).
  Proof.
    intros; apply _.
  Defined.
  (* *)

  (* ===================================== *)
  (* ===================================== *)

  (** ** Initialization *)

  (* ------------------------------------- *)

  (** *** Make bindings for originating terms *)

  
  (** Extend a pr by genr binding(s) for [t]

     This doesn't do any sanity-checking on the term: if passed a
     non-elementary it will dutifully make a Genr binding even though
     that would be stupid *)

  Equations extend_proc_by_gen
    (pr: Proc) (t: Term)  : Proc :=

    extend_proc_by_gen pr t :=      
      match t with
      | Ik k =>  
          let (lpri, lpub) := two_fresh_locs pr in
          pr ++
            [Bind (t, lpri) (Genr (fresh_gen_index pr) (sort_of t)) ;
             Bind ((Ak k), lpub) (PubOf lpri)]
      | _ => pr ++
               [Bind (t, fresh_loc pr) (Genr (fresh_gen_index pr) (sort_of t))]
      end.


  (** extend pr by genr bindings for the terms in [ts] *)
  Equations extend_proc_by_gens
    (pr: Proc) (ts: Terms)  : Proc :=

    extend_proc_by_gens pr [] := pr;
    
    extend_proc_by_gens pr (t::rest) := 
      
      
      extend_proc_by_gens (extend_proc_by_gen pr t) rest .


  (** The sequence of Genr bindings we make for the role *)

  (** We need a utility to filter out from trms any (Ak k) such (Ik k)
  is present in ctxt *)

  Fixpoint exclude_pubs_helper (ctxt trms: list Term) :
    list Term :=
    match trms with 
    | [] => []
    | (Ak k) :: rest => if inb (Ik k) ctxt 
                        then exclude_pubs_helper ctxt rest
                        else (Ak k) :: exclude_pubs_helper ctxt rest
    | t :: rest => t :: exclude_pubs_helper ctxt rest
    end.

  (** Filter out from trms any (Ak k) such (Ik k) is present in trms *)  
  
  Definition exclude_pubs (trms: list Term) :
    list Term := exclude_pubs_helper trms trms.

  Equations initial_gen_bindings (rl: Role):  Proc := 
    
    initial_gen_bindings rl :=
      extend_proc_by_gens
        [] (exclude_pubs (pos_pol_in_role rl)) .
  
  Lemma extend_by_gen_no_new_trace pr t:
    prtrace (extend_proc_by_gen pr t) = prtrace pr.
  Proof.
    apply FunctionalElimination_extend_proc_by_gen.
    intros.
    destruct_all_matches;
      rewrite prtrace_app;    simpl;
      now rewrite app_nil_r.
  Qed.

  Lemma extend_by_gens_no_new_trace pr ts:
    prtrace (extend_proc_by_gens pr ts) = prtrace pr.
  Proof.
    apply (FunctionalElimination_extend_proc_by_gens ).
    intros; auto.
    intros.
    rewrite H.
    apply (extend_by_gen_no_new_trace pr0 t) .
  Qed.

  Lemma initial_gen_no_trace :
    prtrace (initial_gen_bindings rl) = [] .
  Proof.
    simp initial_gen_bindings.
    apply extend_by_gens_no_new_trace.
  Qed.


  (* ------------------------------------- *)

  (** *** Make bindings for Qt terms *)

  (** Extend a pr by a binding(s) for a Qt term *)
  
  Equations extend_proc_by_qt
    (pr: Proc) (t: Term) : Proc :=
    extend_proc_by_qt pr t :=
      match t with 
        (Qt s) => let l := fresh_loc pr in
                  pr ++ [Bind (t,l) (Quote s)]
      | _ => pr
      end.

  (** extend pr by bindings for the terms in [ts], presumably all Qt
  terms *)

  Equations extend_proc_by_qts
    (pr: Proc) (ts: Terms)  : Proc :=

    extend_proc_by_qts pr [] := pr;
    
    extend_proc_by_qts pr (t::rest) := 
      extend_proc_by_qts (extend_proc_by_qt pr t) rest .

  Equations initial_qt_bindings (rl: Role): Proc := 
    initial_qt_bindings rl :=
      extend_proc_by_qts
        [] (quote_terms_in_role rl).


  Lemma extend_by_qt_no_new_trace pr t:
    prtrace (extend_proc_by_qt pr t) = prtrace pr.
  Proof.
    apply FunctionalElimination_extend_proc_by_qt.
    intros.
    destruct_all_matches;
      rewrite prtrace_app;    simpl;
      now rewrite app_nil_r.
  Qed.

  Lemma extend_by_qts_no_new_trace pr ts:
    prtrace (extend_proc_by_qts pr ts) = prtrace pr.
  Proof.
    apply (FunctionalElimination_extend_proc_by_qts ).
    intros; auto.
    intros.
    rewrite H.
    apply (extend_by_qt_no_new_trace pr0 t) .
  Qed.

  Lemma initial_qt_no_trace :
    prtrace (initial_qt_bindings rl) = [] .
  Proof.
    simp initial_qt_bindings.
    apply extend_by_qts_no_new_trace.
  Qed.


  (* ------------- *)

  Definition initial_bindings (rl: Role) : Proc :=
    (initial_gen_bindings rl)  ++
      (initial_qt_bindings rl) .

  Definition initialize : state := 
    {| 
      tr_done := [] ;
      tr_todo := rl;
      the_pr := 
        saturate unv (initial_bindings rl)
    |}.

  Lemma initial_no_trace :
    prtrace (initial_bindings rl) = [] .
  Proof.
    unfold initial_bindings.
    rewrite prtrace_app.
    rewrite initial_gen_no_trace.
    now rewrite initial_qt_no_trace.
  Qed.


  (* ========================================== *)
  (** * Processing Role Events *)
  (* ========================================== *)

  Definition output_msg (t: Term) : list Stmt :=
    [Comm ("output " ++ (show t))].

  Definition input_msg (t: Term) : list Stmt :=
    [Comm ("input "++ (show t))].

  Definition send_msg (ch t: Term) : list Stmt :=
    [Comm ("sending "++ (show t) ++ " on " ++ (show ch))].

  Definition recv_msg (ch t: Term) : list Stmt :=
    [Comm ("receiving "++ (show t) ++ " on " ++ (show ch))].


  (** We do not actually need to saturate at the end of Snd and Ret.
But it is really tedious to prove that we are still saturated after
adding the Evnt statements.

So we call saturate so that we can easily establish that saturation is
invariant.

 And the saturation code will only amount to a check for being
saturated at the first step, so the price is small.  *)

  Definition handle_Ret
    (pr: Proc) (t : Term) : optionE Proc :=
    match first_loc_for pr t with
      NoneE s => NoneE s
    | SomeE tloc =>
        let pr1 := pr 
                     (* ++ (output_msg t) *)
        in
        let pr2 := pr1 ++ [Evnt (Ret tloc)] in
        saturate unv pr2
    end .

  Definition handle_Snd 
    (pr: Proc) (ch t : Term) : optionE Proc :=
    match first_loc_for pr ch with
      NoneE s => NoneE  s  (* shouldn't happen *)
    | SomeE chloc =>
        match first_loc_for pr t with
          NoneE s => NoneE s  (* shouldn't happen *)
        | SomeE tloc =>
            let pr1 := pr
                         (* ++ (send_msg ch t) *)
            in 
            let pr2 := (pr1 ++ [Evnt (Snd chloc tloc)] ) in 
            saturate unv pr2
        end
    end.


  Definition handle_Prm
    (pr: Proc) (t : Term) : optionE Proc :=
    (* new location for the input value *)
    let newl := fresh_loc pr in
    (* new index for the Prm *)
    let input_ind := fresh_input_index pr  in
    (* build an expression for the input value *)
    let input_exp := (Param input_ind) in
    
    (* add the [Param] event *)
    let pr1 := pr 
                 (* ++ (input_msg t) *)
    in
    let pr2 := pr1 ++ [Evnt (Prm newl)] in

    (* add the binding to the input expression *)     
    let pr3 :=  pr2 ++  [(Bind (t,newl) input_exp)] in
    
    (* now saturate *)
    (saturate unv pr3)

  .

  Definition handle_Prm'
    (pr: Proc) (t : Term) :  Proc :=
    (* new location for the input value *)
    let newl := fresh_loc pr in
    (* new index for the Prm *)
    let input_ind := fresh_input_index pr  in
    (* build an expression for the input value *)
    let input_exp := (Param input_ind) in
    
    (* add the [Param] event *)
    let pr1 := pr 
                 (* ++ (input_msg t)  *)
    in
    let pr2 := pr1 ++ [Evnt (Prm newl)] in

    (* add the binding to the input expression *)     
    let pr3 :=  pr2 ++  [(Bind (t,newl) input_exp)] in
    pr3.
  



  Definition handle_Rcv
    (pr: Proc) (ch t : Term) : optionE Proc :=
    (* lookup the channel expression *)
    match first_loc_for pr ch with
      NoneE s => NoneE s (* should never happen *)
    | SomeE lch => 
        (* new location for the read value *)
        let newl := fresh_loc pr in
        (* new index for the Read *)
        let read_ind := fresh_read_index pr  in
        (* build an expression for received value *)
        let read_exp := (Read read_ind) in
        
        (* add the [Rcv] revent *)
        let pr1 := pr 
                     (* ++ (recv_msg ch t) *)
        in
        let pr2 := pr1 ++ [Evnt (Rcv lch newl)] in

        (* add the binding to the read expression *)         
        let pr3 :=  pr2 ++  [(Bind (t,newl) read_exp)] in
        
        (* now saturate *)
        (saturate unv pr3)
    end .

  (** Handle an input, output, send, or receive *)

  Definition handle_action
    (pr: Proc) (act: Act Term) : optionE Proc :=
    match act with
    | Prm t => handle_Prm pr t
    | Ret t => handle_Ret pr t
    | Snd ch t => handle_Snd pr ch t
    | Rcv ch t => handle_Rcv pr ch t
    end.

End Compiling.



(** Perhaps it is misleading to move [a] to the tr_done list in the
    case that  [handle_action] fails, but it makes definitions and
    reasoning a bit simpler.  *)

Definition step (rl: Role) (st :  state) :  state :=
  match st with

  |  (mkState _ _ (NoneE _)) => st

  |  (mkState _ [] _) => st
                           
  |  (mkState d (a::rest) (SomeE pr))  =>
       
       (mkState (d ++ [a]) rest 
          (handle_action rl pr a) )
  end.



Lemma step_char (rl: Role) (st: state) :
  step rl st = st \/
    (exists (d rest : list (Act Term) )
            (a: Act Term) 
            (pr : Proc),
        st = mkState d (a::rest) (SomeE pr)
        /\ step rl st = 
             (mkState (d ++ [a]) rest 
                (handle_action rl pr a) )
    ).
Proof.
  destruct st.
  destruct the_pr0 eqn:e.
  shelve.
  { left. simpl. destruct tr_todo0; easy. }
  Unshelve.
  destruct tr_todo0 eqn:e1.
  { left. simpl. easy. }    
  { right. exists tr_done0; exists l; exists a; exists x.
    split. easy.
    simpl; easy.
  }
Qed.

Lemma no_step  (st :  state) (m: string) :
  the_pr st = NoneE m ->
  forall rl, 
    step rl st = st.
Proof.
  intros H rl.
  destruct st.
  simpl in H.
  rewrite H.
  simpl. destruct tr_todo0; easy.
Qed.

Lemma step_decreasing (rl: Role) :
  decreasing (step rl) measure.
Proof.
  unfold decreasing.
  intros x.
  assert (h:= @step_char rl x).
  destruct h as [h1 | h2].
  { left.  auto. } 
  { right.
    destruct h2 as [d [rest [a [pr [P1 P2]]]]].
    subst.
    unfold measure. simpl.
    lia. }
Qed.

Definition steps_n  (rl: Role) : nat → state → state :=
  loop (step rl).

Definition final_state (rl: Role) : state :=
  steps_n rl (measure (initialize rl)) (initialize rl).

Definition compile (rl: Role) : optionE Proc :=
  the_pr (final_state rl).

Inductive compileR (rl : Role) (pr: Proc) : Prop :=
  compileR1 : compile rl = SomeE pr -> compileR rl pr .



