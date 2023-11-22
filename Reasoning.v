  (* Time-stamp: <Wed 11/22/23 11:22 Dan Dougherty Reasoning.v> 
 *)

From Coq Require Import 
  Relations
  String 
  List 
  Classical_Prop
  Arith.Arith
  Bool.Bool
  Strings.String
  Logic.FunctionalExtensionality
  Lia.

Import ListNotations.

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
  SaturationClass  
  Compile
  roleToRole
.

(** need this technical lemma in several places *)

Lemma list_map_act_map_mono pr x d :
  (forall u l, tdecl_bound pr u l -> tdecl_bound x u l) ->
  List_mapR (Act_mapR (tdecl_bound pr)) d (prtrace pr) ->
  List_mapR (Act_mapR (tdecl_bound x)) d (prtrace pr).
Proof.
  intros.
  eapply List_mapR_mono with 
    (Act_mapR (tdecl_bound pr)).
  - intros. 
    eapply Act_mapR_mono with
      (tdecl_bound pr).
    + intros. apply H; easy.
    + easy.
  - easy.
Qed.

Section Reasoning.

  Variable rl : Role.
  Notation unv := (Subterms_of_role rl).

  (* ------------------------------------------------ *)

  (** * Initial state is invariant *)

  Lemma initial_state_is_invariant :
    invariant rl (initialize rl).
  Proof.
    unfold initialize.
    unfold invariant.
    destruct (saturate unv (initial_bindings rl)) eqn:e.
    shelve.
    split. 
    constructor. constructor. constructor.
    Unshelve.
    easy.
    split.   
    - unfold state_saturated; simpl. 
      eapply saturate_gives_saturated; eauto.
    - split.
      + unfold cursor; now simpl.
      +
        unfold done_related; simpl.
        assert (h:= initial_no_trace).
        assert (h0 := @saturate_trace
                        unv
                        (initial_bindings rl)
                        x e).
        rewrite h in h0.
        rewrite h0.
        constructor.
  Qed.


  (** * Cursor claim *)

  Proposition step_preserves_cursor (st :  state) :
    cursor rl st ->
    cursor rl (step rl st).
  Proof. 
    intros.
    destruct st eqn: e.
    unfold step.
    destruct tr_todo eqn:e1.
    - destruct the_pr eqn:e2; easy.
    - destruct the_pr eqn:e2. 
      + destruct (handle_action rl x a ) eqn:e3.
        --  
          unfold cursor in *. simpl in *.
          rewrite <- app_assoc.
          rewrite <- H.
          rewrite app_inv_head_iff.
          crush. 
        -- unfold cursor in H. simpl in H.
           unfold cursor. simpl.
           crush.
      + easy.
  Qed.


  (** * Saturation claims *)
  

  Lemma handle_action_preserves_saturation  pr act :
    saturated_pr unv pr ->
    forall (x: Proc),
      handle_action rl pr act = SomeE x -> 
      saturated_pr unv x.
  Proof.
    intros H1 x H2. 
    unfold handle_action in *.
    destruct act.
    - (* Prm *)
      unfold handle_Prm in *.
      eapply saturate_gives_saturated;  eauto.

    -  (* Ret *) 
      (* assert (h1:= @handle_Ret_same_internals pr t x H2). *)
      (* symmetry in h1. *)
      unfold handle_Ret in *.
      destruct (first_loc_for pr t).
      eapply saturate_gives_saturated;  eauto. easy.
 
    - (* Rcv *)
      unfold handle_Rcv in *.
      destruct (first_loc_for pr t).
      + eapply saturate_gives_saturated; eauto.
      + easy.
 
    - (* Snd *) 
      unfold handle_Snd in * .
      destruct (first_loc_for pr t) eqn:e. 
      destruct (first_loc_for pr t0) eqn:e0. 
      inv H2. 
      + eapply saturate_gives_saturated; eauto.  
      + easy.
      + easy.
  Qed.



  (* ------------------------------------------------ *)
  (** * Trace claims *)
  (* ------------------------------------------------ *)


  Lemma handle_Prm_trace_results pr t x :
    handle_Prm rl pr t = SomeE x  ->
    exists (l: loc),
      prtrace x = prtrace pr ++ [(Prm l)]
      /\
        tdecl_bound x t l .
  Proof. 
    intros H.
    unfold handle_Prm in H. 
    exists (fresh_loc pr).
    assert (h1:= saturate_trace H).
    (* do 3 rewrite prtrace_app in h1.  *)
    do 2 rewrite prtrace_app in h1. 
    simpl in h1.
    (* do 2 rewrite app_nil_r in h1. *)
    rewrite app_nil_r in h1.
    split.
    - easy.
    -
      clear h1.
      apply saturate_superset in H. 
      remember
        (Bind (t, fresh_loc pr)
           (Param (fresh_input_index pr)))
        as b.
      exists b.
      split.
      + apply H.
        eapply in_or_app.
        right. auto.
      + subst. tauto.
  Qed.


  Lemma handle_Rcv_trace_results pr ch t x :
    handle_Rcv rl pr ch t = SomeE x  ->
    exists (lch lt: loc),
      prtrace x = prtrace pr ++ [Rcv lch lt]
      /\ tdecl_bound x ch lch
      /\ tdecl_bound x t lt  .
  Proof.
    intros H.
    unfold handle_Rcv in H.

    (* discard contradictory case *)
    destruct (first_loc_for pr ch) eqn:e .
    shelve. easy.
    Unshelve.
    
    exists x0; exists (fresh_loc pr). 
    assert (h1:= saturate_trace H).
    do 2 rewrite prtrace_app in h1.
    (* simpl in h1.  *)
    (* rewrite prtrace_app in h1. *)
    (* do 2 rewrite app_nil_r in h1. *)
    (* simpl in h1. *)
    split.
    - rewrite h1. simpl.
      now rewrite app_nil_r.

    - clear h1.
      apply saturate_superset in H.

      apply subset_app_elim in H.
      destruct H as [H1 H2].
      apply subset_app_elim in H1.
      destruct H1 as [H3 H4].
      (* apply subset_app_elim in H3. *)
      (* destruct H3 as [H5 H6]. *)
      split.
      + 
        apply tdecl_mono with pr;
          auto.
        apply first_loc_tdecl. easy.

      + apply subset_in in H2.
        exists (Bind (t, fresh_loc pr) (Read (fresh_read_index pr))).
        split; eauto.
  Qed.


  Lemma handle_Ret_trace_results pr t prfinal :
    handle_Ret rl pr t = SomeE prfinal  ->
    exists (l: loc),
      prtrace prfinal = prtrace pr ++ [Ret l]
      /\ tdecl_bound prfinal t l  .
  Proof.
    intros H.
    unfold handle_Ret in H.
    
    (* discard contradictory case *)
    destruct (first_loc_for pr t) eqn:e .
    shelve. easy.
    Unshelve.
 
    assert (h1:= saturate_trace H).
    rewrite prtrace_app  in h1.
    simpl in h1.
    (* rewrite app_nil_r in h1. *)

    exists x.
    split.
    - (* trace is ok *) 
      easy.
    - (* binding is ok *)
      assert (h2: tdecl_bound pr t x).
      { apply first_loc_tdecl; auto. }
      assert (h3: subset pr prfinal).
      { apply saturate_superset in H.
        
        apply subset_app_elim in H.
        destruct H as [H1 H2].
        easy. }
      eapply tdecl_mono; eauto.
Qed.


  Lemma handle_Snd_trace_results pr ch t x :
    handle_Snd rl pr ch t = SomeE x  ->
    exists (lch lt: loc),
      prtrace x = prtrace pr ++ [Snd lch lt]
      /\ tdecl_bound x ch lch
      /\ tdecl_bound x t lt  .
  Proof.
    intros H. 
    unfold handle_Snd in H.
    
    (* discard contradictory case *)
    destruct (first_loc_for pr ch) eqn:ech .
    shelve. easy.
    Unshelve.

    (* discard contradictory case *)
    destruct (first_loc_for pr t) eqn:et .
    shelve. easy.
    Unshelve.

    assert (h1:= saturate_trace H).
    rewrite prtrace_app  in h1.
    simpl in h1.

    exists x0; exists x1.
    split.
    - (* trace is ok *) 
      easy.
    - (* binding is ok *)
      assert (h2: tdecl_bound pr ch x0).
      { apply first_loc_tdecl; auto. }

      assert (h3: tdecl_bound pr t x1).
      { apply first_loc_tdecl; auto. }
      split.

      + assert (h4: subset pr x).
      { apply saturate_superset in H.
        
        apply subset_app_elim in H.
        destruct H as [H1 H2]; auto.
      }
      eapply tdecl_mono; eauto.

   + assert (h4: subset pr x).
      { apply saturate_superset in H.
        
        apply subset_app_elim in H.
        destruct H as [H1 H2]; auto.
      }
      eapply tdecl_mono; eauto.
Qed.


  (** * Miscellaneous technical things *)

  (** Handling actions doesn't lose anything from the proc *)

  Lemma handle_action_increasing pr a x :
    handle_action rl pr a = SomeE x  ->
    subset pr x.
  Proof.
    intros H.
    unfold handle_action in *.
    destruct a.

    - (* Prm *)
      unfold handle_Prm in *.
      apply saturate_superset in H.
      apply subset_app_elim in H.
      destruct H.

      apply subset_app_elim in H.
      destruct H as [H1 H2]; auto.

    - (* Ret *)
      unfold handle_Ret in *.
      destruct (first_loc_for pr t).
      apply saturate_superset in H.
      (* rewrite <- app_assoc in H. *)
      apply  subset_app_elim in H.
      tauto.
      easy.

    - (* Rcv *)
      unfold handle_Rcv in *.
      destruct (first_loc_for pr t).

      apply saturate_superset in H.
      apply subset_app_elim in H.
      destruct H as [H1 H2].
      apply subset_app_elim in H1.
      destruct H1 as [H3 H4].
      (* apply subset_app_elim in H3. *)
      tauto. easy.

    - (* Snd *)
      unfold handle_Snd in *.
      destruct (first_loc_for pr t);
        destruct (first_loc_for pr t0).
      + apply saturate_superset in H.
        (* rewrite <- app_assoc in H. *)
        apply  subset_app_elim in H.
      tauto.
      + easy.
      + easy.
      + easy.
  Qed.
  #[local] Hint Resolve handle_action_increasing : core.


  Lemma handle_action_tdecls pr a x :
    handle_action rl pr a = SomeE x  ->
    forall u l,
      tdecl_bound pr u l ->
      tdecl_bound x u l.
  Proof.
    intros H1 u l H2.
    assert (h1:= @handle_action_increasing pr a x H1).
    assert (h2:= tdecl_mono pr x h1 ).
    apply h2. easy.
  Qed.


  (* ------------------------------------------------ *)


  

  Proposition step_preserves_state_saturation (st : state) :
    state_saturated rl st ->
    state_saturated rl (step rl st).
  Proof.
    intros.
    destruct st eqn:e1.
    simpl in *.
    destruct (the_pr) eqn:e3.
    - assert (h: saturated_pr unv x). 
      { apply H. }
      destruct (tr_todo) eqn:e2.
      + easy.
      + destruct (handle_action rl x a) eqn:e.
        assert (h0:= @handle_action_preserves_saturation x a h x0 e).
        apply h0.
        constructor.

    - destruct (tr_todo) eqn:e2.
      + easy.
      + easy.
  Qed.


  (* -------------------------------------------- *)

  (** * Trace claims *)

  Lemma output_msg_trace pr t :
    prtrace (pr ++ (output_msg t)) =
      prtrace pr.
  Proof.
    induction pr as [| a rest IH]; simpl; auto.
    destruct a; try easy.
    rewrite prtrace_app.
    simpl.
    now rewrite app_nil_r.
  Qed.


  Lemma input_msg_trace pr t :
    prtrace (pr ++ (input_msg t)) =
      prtrace pr.
  Proof.
    induction pr as [| a rest IH]; simpl; auto.
    destruct a; try easy.
    rewrite prtrace_app.
    simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma send_msg_trace pr ch t :
    prtrace (pr ++ (send_msg ch t)) =
      prtrace pr.
  Proof.
    induction pr as [| a rest IH]; simpl; auto.
    destruct a; try easy.
    rewrite prtrace_app.
    simpl.
    now rewrite app_nil_r.
  Qed.


  Lemma recv_msg_trace pr ch t :
    prtrace (pr ++ (recv_msg ch t)) =
      prtrace pr.
  Proof.
    induction pr as [| a rest IH]; simpl; auto.
    destruct a; try easy.
    rewrite prtrace_app.
    simpl.
    now rewrite app_nil_r.
  Qed.

  

  (** ** done_related invariant is  preserved *)
  

  Proposition step_preserves_done_related (st : state) :
    done_related st -> 
    done_related (step rl st).
  Proof. 
    intros. 
    assert (h:= step_char rl st).
    destruct h as [h1 | h2].
    - rewrite h1; auto.
    - destruct h2 as [d [rest [a [pr [P1 P2]]]]].
      rewrite P1 in *.      
      rewrite P2.   
      unfold done_related in *. simpl in *. 
      destruct (handle_action rl pr a) eqn:e.
      shelve. easy.      
      Unshelve.
      clear P2.
      destruct a.

      -- (* Prm *)
        unfold handle_action in *.
        unfold done_related in * ; simpl in *.
        subst.
        assert (h:= @handle_Prm_trace_results pr t x e).
        destruct h as [l [P Q]].      
        unfold done_related in *.
        rewrite P.  
        apply List_mapR_snoc.
        {
          apply list_map_act_map_mono.  
          {
            assert (h1:= @handle_action_increasing 
                           pr (Prm t) x e).
            assert (h2:= @tdecl_mono pr x h1).
            apply h2.
          }
          easy.
        }
        now constructor.

      -- (* Ret *)
        unfold handle_action in *.
        unfold done_related in * ; simpl in *.
        subst.
        assert (h:= @handle_Ret_trace_results  pr t x e).
        destruct h as [l [P1 P2]].
        unfold done_related in *.
        simpl in *.
        rewrite P1.
        apply List_mapR_snoc.
        apply  list_map_act_map_mono.
        assert (h1:= @handle_action_increasing pr (Ret t) x e).
        assert (h2:= @tdecl_mono pr x h1).
        apply h2.
        easy.
        now constructor.
        
      -- (* Rcv *)
        unfold handle_action in *.
        unfold done_related in * ; simpl in *.
        subst.
        assert (h:= @handle_Rcv_trace_results pr t t0 x e) .
        destruct h as [lch [lt [P [Q1 Q2]]]].
        unfold done_related in *. simpl in  *.
        rewrite P. 
        apply List_mapR_snoc. 
        {
          apply list_map_act_map_mono.
          { 
            assert (h2:= @handle_action_increasing 
                           pr (Rcv t t0) x e).
            now apply tdecl_mono.
          } 
          easy.
        }
        now constructor.

      -- (* Snd *)
        unfold handle_action in *.
        unfold done_related in * ; simpl in *.
        subst.
        assert (h:= @handle_Snd_trace_results
                      pr t t0 x e).
        destruct h as [lch [lt [P1 [P2 P3]]]].
        unfold done_related in *.
        simpl in *.
        rewrite P1.
        apply List_mapR_snoc.
        {
          apply  list_map_act_map_mono.
          { 
            assert (h1:= @handle_action_increasing pr (Snd t t0) x e).
            assert (h2:= @tdecl_mono pr x h1).
            apply h2.
          }
          easy.
        }
        now constructor.
  Qed.



  Theorem step_invariant (st: state) :
    invariant rl st ->
    invariant rl (step rl st) .
  Proof.
    intros H.
    destruct H as [Hsat [Hcur Hdone]].
    assert (hsat:= 
              @step_preserves_state_saturation st Hsat ).
    assert (hcur:= 
              @step_preserves_cursor st Hcur).
    assert (hdr:= 
              @step_preserves_done_related st Hdone).
    split; auto.
  Qed.



  Theorem steps_n_invariant (st: state) :
    invariant rl st ->
    forall k, invariant rl (steps_n rl k st) .
  Proof.
    intros H k.
    apply ( @Iteration.prove_invariant 
              (state)
              (step rl)
              (invariant rl)
              (step_invariant)
              st
              H 
              k ).
  Qed.

  
  Theorem final_state_invariant :
    invariant rl (final_state rl).
  Proof.
    assert (h:= initial_state_is_invariant).
    apply (steps_n_invariant h). 
  Qed.


  (** * A successful final state is a fixed point for step *)

  Theorem fixed_final :
    step rl (final_state rl) = (final_state rl).
  Proof.
    unfold final_state.
    assert (h:= @fixed_max_loop _ (step rl)
                  measure
                  (step_decreasing rl)
           ).
    apply h.
  Qed.
  

  Lemma step_noop (st: state) :
    step rl st = st ->
    ( (exists s, the_pr st = NoneE s)
      \/ tr_todo st = []
    ).
  Proof.
    intros H.
    destruct st.
    destruct (the_pr) eqn:e.
    shelve.
    { simpl in H. destruct tr_todo.
      - left. exists s. now simpl. 
      - left. exists s. now simpl.  }
    Unshelve.
    right.
    simpl.


    destruct (tr_todo) eqn:e1.
    + easy. 
    + simpl in H.
      injection H; intros.
      symmetry in H1.
      assert (h:= list_cycle H1).
      easy.
  Qed.

  Lemma tr_todo_of_final pr  :
    compile rl = SomeE pr ->
    (tr_todo (final_state rl) = []).
  Proof.
    intros H. 
    unfold compile in *.
    assert (f:= fixed_final).
    assert (n:= @step_noop (final_state rl)
                  f).
    destruct n as [n1 | n2].
    { destruct n1 as [s Q]. congruence. }
    easy.
  Qed.

  Lemma tr_done_of_final pr  :
    compile rl = SomeE pr ->
    (tr_done (final_state rl))
    = rl.    
  Proof.
    intros H.
    assert (f:= final_state_invariant ).
    unfold invariant in f.
    destruct f as [f1 [f2 f3]].
    unfold cursor in f2.

    assert (h:= @tr_todo_of_final pr H).
    rewrite h in f2.
    rewrite app_nil_r in f2.
    easy.
  Qed.


  Lemma pr_of_final pr  :
    compile rl = SomeE pr ->
    (the_pr (final_state rl) = SomeE pr).
  Proof.
    intros H.
    unfold compile in H.
    destruct (final_state rl ) eqn:e1.
    simpl in *.
    easy.
  Qed.


  Definition traces_line_up pr : Prop :=
    List_mapR (Act_mapR (tdecl_bound pr)) rl (prtrace pr) .

  
  Theorem compile_traces pr :
    compileR  rl pr ->
    traces_line_up pr.
  Proof.
    intros H. inv H.
    assert (h1:= final_state_invariant ).
    destruct h1 as [a1 [a2 a3]].
    unfold done_related in a3.
    assert (h2:= @pr_of_final pr H0).
    assert (h3:= @tr_done_of_final pr H0 ).
    rewrite h2 in a3.
    rewrite h3 in a3.
    easy.
  Qed.

  (** More convenient version using [tl] instad of [tdecl_bound] *)

  Definition traces_line_up_tl pr : Prop :=
    List_mapR (Act_mapR (tl pr)) rl (prtrace pr) .
  
  Theorem compile_traces_tl pr :
    compileR  rl pr ->
    traces_line_up_tl pr.
  Proof.
    intros H.
    hnf.
    apply compile_traces in H. hnf in H.
    eapply List_mapR_iff; eauto.
    intros; apply Act_mapR_iff.
    intros; apply tl_tdecl_iff.
  Qed. 

 
  Theorem compile_saturated pr :
    compileR rl  pr  ->
    saturated_pr unv pr.
  Proof.
    intros Hc.  inv Hc.
    hnf.


    assert (h1:= final_state_invariant ).
    destruct h1 as [a1 [a2 a3]].
    hnf in a1.
    assert (h2:= @pr_of_final pr H).
    now rewrite h2 in a1.
  Qed.


End Reasoning.

Section SatdClassInstance.

  Variable rl : Role.
  Let unv := (Subterms_of_role rl).

  Variable pr: Proc.
  Hypothesis H : compileR rl pr.


(* destructing closedness 
   destruct Hc as
   [EL [ER [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]]].
*)
 
  Lemma compile_pair_analyze : ax_pair_analyze pr.
  Proof.
    intros t1 t2 l e H1 H2.
    assert (h:= @compile_saturated rl pr H).
    destruct h as [Hc [Hj Hs]].
    destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].
    
    assert (h1:= @pairE_closed_then pr E t1 t2 l e H1).
    destruct h1 as [is_pair_exp | [h11 h12]]; auto. 
    - congruence.
    - split.
    {
      now apply term_exp_in_proc_elim in h11.
    }
    { 
      now apply term_exp_in_proc_elim in h12.
    }
Qed.
  #[local] Hint Resolve compile_pair_analyze: core.

 Lemma compile_decryption_keys : ax_decryption_keys pr.
   Proof.
    hnf. 
    intros p k le ee H1 H2.
 
    assert (h:= @compile_saturated rl pr H).
    destruct h as [Hc [Hj Hs]].
    destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].

    assert (h1:= @encrE_closed_then pr eE p k le ee H1 H2).
    unfold encryptions_justified in Hs.
    specialize (Hs (Bind  (En p k, le) ee) H1).
    unfold encryption_justified in Hs.
    destruct Hs as [N | Y]; try congruence.
    destruct Y as [lkd [ekd Q]].
    
    exists (inv k); exists lkd; exists ekd.
    split; auto.
Qed.
    
#[local] Hint Resolve compile_decryption_keys: core.


Lemma compile_decryption : ax_decryption pr.
Proof.
hnf.
intros p k le ee Hbt He.
intros kd lkd ekd Hbk Hinv.
assert (h:= @compile_saturated rl pr H).
destruct h as [Hc [Hj Hs]].
destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].

{
  (* proved in [Saturation.v] *)
  assert (h1:= @encrE_closed_then pr eE p k le ee Hbt
         He kd lkd ekd Hbk Hinv).
  apply term_exp_in_proc_elim in h1.
  auto.
}
Qed.
#[local] Hint Resolve compile_decryption: core.

 Lemma compile_hash_check : ax_hash_check pr.
   Proof.
     hnf.  
     intros t lt lh et eh H1  H3.

    assert (h:= @compile_saturated rl pr H).


    destruct h as [Hc [Hj Hs]].    
    destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].

    assert (h1:= @hashChck_closed_then pr  hC t lh lt eh et H1 H3 ).  


  apply h1.
   Qed.
#[local] Hint Resolve compile_hash_check: core.


Lemma compile_hash_justified: ax_hash_justified pr.
   Proof. 
    hnf.
    intros p lh eh Hin.

    assert (h:= @compile_saturated rl pr H).
    destruct h as [Hc [Hj Hsh]].    
    destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].
    
    unfold hashes_justified in *.
    specialize (Hj (Bind (Hs p, lh) eh) Hin).
    unfold hash_justified in Hj.
    destruct Hj as [lt [et Q]].
    exists lt; exists et. easy.
Qed.
#[local] Hint Resolve compile_hash_justified: core.


 Lemma compile_sameness : ax_sameness pr.
 Proof.
   hnf.
   intros t loc1 loc2 e1 e2 He H1 H2 .

   assert (h:= @compile_saturated rl pr H).
   destruct h as [Hc [Hj Hs]].
   destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].

  (* proved in [Saturation.v] *)
  assert (h1:= @sameChck_closed_then pr 
         smeC  t loc1 loc2 e1 e2
         He H1 H2 ).
  destruct (decide (loc1=loc2)).
   - subst.
     apply rst_refl.
   - easy.
Qed.
#[local] Hint Resolve compile_sameness: core.

 Lemma compile_sortChck : ax_sort_check pr.
   Proof.
     hnf.
     intros t l e H1 H2.
     
     assert (h:= @compile_saturated rl pr H).
     destruct h as [Hc [Hj Hs]].
     destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]]. 

  assert (h1:= @strong_ax_sort_check pr srtC
         t l e H1 H2).
  destruct h1 as [l' [e' [P1 [P2 P3]]]].

  exists l'; exists e'. tauto.
Qed.
#[local] Hint Resolve compile_sortChck: core.

Lemma compile_qotChck : ax_qotChck pr.
   Proof.
     hnf.
     intros s l e H1 . 

     assert (h:= @compile_saturated rl pr H).
     destruct h as [Hc [Hj Hs]].
     destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].

     assert (h:= @qotChck_closed_then pr
                   qC s l e H1).
     auto.
Qed.
#[local] Hint Resolve compile_qotChck: core.


 Lemma compile_key_pairs : ax_key_pairs pr.
   Proof.
     hnf .
     intros t1 t2 l1 l2 e1 e2 Hp H1 H2.
     assert (h:= @compile_saturated rl pr H).
     destruct h as [Hc [Hj Hs]].
     destruct Hc as [E [pI [eE [eI [hI [hC [smeC [srtC [qC iC ]]]]]]]]].

     assert (h:= @kyprChck_closed_then pr). 
     eapply h; eauto.
Qed.
#[local] Hint Resolve compile_key_pairs: core.
  

(* have to keep this in the section since the Hints don't work outside.  
*)

 Instance pr_is_satd : @Satd pr. 
  Proof. 
    constructor.
    assert (h:= @compile_saturated rl pr H). 
    destruct h as [Hc [Hj Hs]].
    destruct Hc. 
    all: auto. 
Defined.

End SatdClassInstance.

