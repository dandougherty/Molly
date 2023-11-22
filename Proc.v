(* Time-stamp: <Wed 11/22/23 11:21 Dan Dougherty Proc.v> *)
From Coq Require Import
  String 
  List
  Relations
.

From RC Require Import
  CpdtTactics
  TacticsMatch
  Utilities
  ListUtil
  Decidability
  Act
  Sorts
  Term
  (* ATerm *)
  Role
.
Unset Implicit Arguments.

(** *** Locations and tdecls *)

Inductive loc := L : nat -> loc.

(** *** loc equality *)

Scheme Equality for loc.

(** Defines 
 [loc_beq] and
 [loc_eq_dec : ∀ x y : loc, {x = y} + {x ≠ y}] 
 internal_loc_dec_bl : 
 ∀ x y : loc, loc_beq x y = true → x = y]

 [internal_loc_dec_lb]:
 ∀ x y : loc, x = y → loc_beq x y = true 

*)


(** Thus loc is decidable *)

#[export] Instance loc_eqDec : EqDecision loc
  := loc_eq_dec.

(** And the internal functions imply loc is an instance of EqbDec *)

Lemma beq_eq_loc : forall x y, 
    if loc_beq x y then x = y else x <> y.
Proof.
  intros.
  assert (abl := @internal_loc_dec_bl x y).
  assert (alb := @internal_loc_dec_lb x y).
  destruct (loc_beq x y); auto. intros F. 
  firstorder; easy.
Qed.

#[global] Instance loc_eqbdec : EqbDec loc :=
  { beq:= loc_beq;
    beq_eq := beq_eq_loc
  }.

(** Now since loc is an Decidability.EqbDec, we have reflection [Decidability.beq_reflect]
 *)


(** Show *)

Open Scope string_scope.
#[global] Instance show_loc : Show loc :=
  {
    show x := 
      match x with
        L i => "L " ++(show i)
      end}.
Close Scope string_scope.

(** A default location *)

Definition default_loc := L 0.

Definition loc_ltb (l1 l2 : loc) : bool :=
  match (l1,l2) with
    (L i, L j) => Nat.ltb i j
  end .



(** Tdecls *) 
Definition tdecl: Set := Term * loc.

(** *** tdecl equality *)

Definition tdecl_dec:
  forall x y: tdecl, {x = y} + {x <> y}.
Proof.
  intros. 
  decide equality. decide equality. decide equality.
  (* apply eqDecision_term. *)
  apply Term_eq_dec.
Defined.


#[export] Instance eqDecision_tdecl : EqDecision tdecl
  := tdecl_dec.
#[global] Hint Resolve tdecl_dec : core.

Definition tdecl_beq (x y: tdecl) : bool :=
  match x, y with
    | (t1,l1) , (t2, l2) => beq t1 t2 && beq l1 l2
  end.

Lemma beq_eq_tdecl : forall x y, 
    if tdecl_beq x y then x = y else x <> y.
Proof.
  intros.
  destruct (tdecl_beq x y) eqn:eq1.
  {
  destruct x; destruct y.
  unfold tdecl_beq in *.
  destruct (beq_reflect t t0);
  destruct (beq_reflect l l0); subst; 
  simpl in *; auto; try easy.
  }
  {
    destruct x; destruct y.
    unfold tdecl_beq in *.
    destruct (beq_reflect t t0);
      destruct (beq_reflect l l0); subst; 
      simpl in *; auto; try easy; try congruence.
}
Qed.

#[global] Instance tdecl_eqbdec : EqbDec tdecl :=
  { beq:= tdecl_beq;
    beq_eq := beq_eq_tdecl
  }.



(** *** Expressions *)
Inductive Expr: Set :=
| Pair: loc -> loc -> Expr   
| Encr: loc -> loc -> Expr   
| Hash: loc -> Expr           

| Frst: loc -> Expr           
| Scnd: loc -> Expr           
| Decr: loc -> loc -> Expr   

| Quote: string -> Expr
| PubOf: loc -> Expr
| Genr: nat -> sort -> Expr                  
| Param: nat -> Expr
| Read: nat -> Expr
.         

(** *** Statements *)

Inductive Stmt: Type :=
| Bind: tdecl -> Expr -> Stmt  
                           
| Evnt : (Act loc) -> Stmt

(* value in 1st loc = value in 2nd *)
| Csame: loc -> loc -> Stmt   

(* value in 1st loc is hash of value in 2nd *)
| Chash : loc -> loc -> Stmt

(* values in the two locs make a key pair, with the public key first *)
| Ckypr: loc -> loc -> Stmt   

(* value in the loc has the sort given *)
| Csrt: loc -> sort -> Stmt   

(* value in the loc is the string given *)
| Cquote: loc -> string -> Stmt   

(* comment *)
| Comm: string -> Stmt
.

Definition Proc := (list Stmt).
Definition Stmts := (list Stmt).

(** * Equivalance closure of (speaking informally) the "Same" relation *)

(** there is a "Same ptr" from location 1 to location 2 *)

Definition same_ptr (pr: Proc) (l1 l2 : loc) : Prop  :=
  In (Csame l1 l2) pr.

(** the equivalence closure of same_ptr *)

Definition same_linked (pr: Proc) ( l1 l2 : loc) : Prop :=
  clos_refl_sym_trans loc (same_ptr pr) l1 l2 .


(** ** Decidable equality *)


(** *** tdecl *)

(** *** Expr *)

#[export] Instance eqDecision_expr : EqDecision Expr.
Proof.  repeat solve_decision.
Defined.

#[export] Instance eqDecision_stmt : EqDecision Stmt.
Proof.  repeat solve_decision.
Defined.

#[export] Instance eqDecision_stmts : EqDecision (list Stmt).
Proof. apply Decidability.list_eq_dec. Defined.  


(* ---------------------------------- *)
(** ** Taxonomy of Expr *)

Definition is_pair_expb (exp: Expr) : bool :=
  match exp with
  | Pair _ _ => true
  | _ => false
  end.

Definition is_pair_exp (exp: Expr) : Prop :=
  exists l1 l2, exp = Pair l1 l2.
#[export] Instance is_pair_exp_dec e :
  Decision (is_pair_exp e).
Proof.
  intros.  hnf. unfold is_pair_exp. 
  destruct e. 
  left; exists l; exists l0; easy.
  all: right; intros F;
    destruct F as [l1 [l2 P ] ] ; congruence.
Defined.

Definition is_encr_expb (exp: Expr) : bool :=
  match exp with
  | Encr _ _ => true
  | _ => false
  end.

Definition is_encr_exp (exp: Expr) : Prop :=
  exists l1 l2, exp = Encr l1 l2.
Global Instance is_encr_exp_dec e :
  Decision (is_encr_exp e).
Proof.
  intros.  hnf. 
  (* unfold is_pair_exp.  *)
  destruct e. 
  all: try (right; intros F;
            destruct F as [l1 [l2 P ] ]; congruence).
  left; exists l; exists l0; easy.
Defined.

Definition is_hash_expb (exp: Expr) : bool :=
  match exp with
  | Hash _ => true
  | _ => false
  end.

Definition is_hash_exp (exp: Expr) : Prop :=
  exists l, exp =  Hash l.
Global Instance is_hash_exp_dec e :
  Decision (is_hash_exp e).
Proof.
  intros.  hnf. 
  destruct e. 
  all: try (right; intros F;
            destruct F; congruence).
  left; exists l; easy.
Defined.

Definition is_quote_exp (exp: Expr) : Prop :=
  exists (s: string), exp =  Quote s.
Global Instance is_quote_exp_dec e :
  Decision (is_quote_exp e).
Proof.
  intros.  hnf. 
  destruct e. 
  all: try (right; intros F;
            destruct F; congruence).
  left; exists s; easy.
Defined.


Definition is_quote_expb (exp: Expr) : bool :=
  match exp with
  | Quote _ => true
  | _ => false
  end.

Definition is_I_expr (exp: Expr) : bool :=
  match exp with
  | Pair _ _ => true
  | Encr _ _ => true
  | Hash _ => true
  | Quote _ => true
  | _ => false
  end
.         

(** *** Genr indices *)

(** The largest gen index not usd in pr *)
(** But: initialize with 0, so [fresh_gen_index]
    will start with 1.
 *)
    
Fixpoint max_gen_index (pr: Proc) : nat := 
   match pr with
     [] => 0
   | (Bind (_ , _) (Genr i _)) :: rest =>
       S (max_gen_index rest)
   | _ :: rest => (max_gen_index rest)
   end.

Definition fresh_gen_index (pr:  Proc) : nat :=
  S (max_gen_index pr) .


(* ---------------------------------- *)

(** ** Extract the bindings in a Proc *)

Definition is_binding (st: Stmt) : bool :=
  match st with
  | Bind _ _ => true
  | _  => false
  end.

Definition is_binding_for (t: Term) (st: Stmt) : bool :=
  match st with
  | Bind (t,_) _ => true
  | _  => false
  end.


Definition bindings (pr: Proc) : list Stmt :=
  filter is_binding pr.


Fixpoint locs_of pr : list loc :=
  match pr with 
    [] => []
  | (Bind (_ , l) _ ) :: rest => 
      l :: (locs_of rest)
  | _ :: rest => (locs_of rest)
  end.

Lemma locs_of_append pr ls :
  locs_of (pr++ls) =
    (locs_of pr) ++ (locs_of ls).
Proof.
  induction pr as [| s rest IH]; simpl; auto.
  - destruct_all_matches.
    rewrite IH; auto.
Qed.

Corollary in_loc_append_L pr ls l :
  In l (locs_of pr) ->
  In l (locs_of (pr++ls)).
Proof.
  intros H.
  rewrite locs_of_append; auto.
Qed.

Corollary in_loc_append_R pr ls l :
  In l (locs_of ls) ->
  In l (locs_of (pr++ls)).
Proof.
  intros H.
  rewrite locs_of_append ; auto.
Qed.

(** The largest location not bound in pr *)
(** But: initialize with 0, so [fresh_loc]
    will start with 1.
 *)
    
Fixpoint max_loc (pr: Proc) : loc := 
   match pr with
     [] => L 0
   | (Bind (_ , (L i)) _) :: rest =>
       match (max_loc rest) with
         L m => 
           L (max m i)
       end
   | _ :: rest => (max_loc rest)
   end.

Definition next_loc (l: loc) : loc :=
  match l with L i => L (S i)
  end.

Definition fresh_loc (pr:  Proc) : loc :=
  next_loc (max_loc pr) .

(** Convenient when we need two fresh locations, 
    perhaps with intervening statments, this keeps the bookkeepping simpler 
    than two calls to [fresh_loc] 
*)
Definition two_fresh_locs (pr:  Proc) : loc*loc :=
  let newloc := next_loc (max_loc pr) in 
  (newloc , next_loc newloc).

(* ======================= *)

(** ** First loc for a term *)

(** some flailing around here...could be streamlined *)

Fixpoint first_loc_for
  (pr: Proc)   (t: Term): optionE loc :=
  match pr with 
    [] => NoneE ("failed first_loc_for: " ++ (show t))
  | (Bind (t', l) e) :: rest => 
      match decide (t=t') with
      | left _ =>  SomeE l 
      | right _ => first_loc_for rest t
      end

  | _ :: rest =>  first_loc_for rest t
  end.


Lemma first_loc_exists pr t l e  :
  In (Bind (t,l) e) pr ->
  forall s, first_loc_for pr t <> NoneE s.

Proof.
  intros. induction pr. simpl in H; tauto.
  simpl in H. destruct H. 
  - subst; simpl.  destruct (decide (t=t)); easy.
  - pose proof (IHpr H).
    intros F.
    (* unfold first_loc_for in F. *)
    destruct a.
    simpl in F.
    destruct t0.
    destruct (decide (t=t0)).
    subst; easy. cong.
    all: simpl in F; easy.
Qed.

Lemma in_first_loc pr t l e :
  In (Bind (t,l) e) pr ->
  exists l',  first_loc_for pr t = SomeE l'.

Proof.
  intros.
  assert (h:= @first_loc_exists pr t l e H).
  destruct (first_loc_for pr t) eqn:eq1; auto.
  exists x; auto. cong.
Qed.


Lemma first_loc_for_elim_None pr t s :
  first_loc_for pr t = NoneE s ->
  forall (l: loc) (e: Expr), 
    ~ In (Bind (t,l) e) pr.

Proof.
  intros H l e F.
  apply in_first_loc in F.
  destruct F as [l' P].
  congruence.
Qed.

Proposition first_loc_for_elim pr t l :
  first_loc_for pr t = SomeE l ->
  exists (e: Expr), In (Bind (t,l) e) pr.

Proof.
  intros H.
  induction  pr as [| smt rest IH ] .
  - inv H.
  - destruct  smt as 
      [[ t0 l0 ] e0 | ev |l1 l2 |l1 l2| l1 l2| l0 s | l0 s | s ] .

    { (* first stmt is a Bind *)
      destruct (decide (t = t0)) eqn:et.
      { (* t=t0 *)
        simpl in H. rewrite et in H. 
        inv H.
        exists e0. auto. }
      { (* t<>t0 *)
        simpl in H.
        rewrite et in H. 
        assert (h1:= IH H).
        destruct h1 as [e Hin ] .
        exists e. auto.
      }
    }
    (* first stmt is not a Bind, use IH *)
    all : (simpl in H;
           assert (h1:= IH H);
           destruct h1 as [e Hin];
           exists e; auto).
Qed.


Proposition first_loc_for_intro pr t l e:
  In (Bind (t,l) e) pr ->
  exists (lf: loc) (ef: Expr), 
    In (Bind (t,lf) ef) pr /\
      first_loc_for pr t = SomeE lf .

Proof.
  intros.
  assert (h1:= first_loc_exists pr t l e H).
  apply not_NoneE_SomeE in h1.
  destruct h1 as [lf P].
  assert (h2:= first_loc_for_elim pr t lf P ).
  destruct h2 as [ef Q].
  exists lf ; exists ef. tauto.
Qed.

(** *** first_loc with a default value *)

Fixpoint first_loc_for_default
  (pr: Proc) (t: Term) :  loc :=
  match pr with 
    [] => default_loc
  | (Bind (t', l) e) :: rest => 
      match decide (t=t') with
      | left _ =>  l 
      | right _ => first_loc_for_default rest t
      end

  | _ :: rest =>  first_loc_for_default rest t 
  end.

(** just a shorthand for readability) *)

Definition a_loc_for (pr: Proc) (t: Term) :=
  first_loc_for_default pr t.

(** If we know there is some first_loc for t then
first_loc_for_default finds it *)

Lemma first_loc_for_def_works pr t l :
  first_loc_for pr t = SomeE l ->   
  first_loc_for_default pr t = l .
Proof.
  intros H.
  induction pr as [| a rest IH]; auto.
  - simpl in H. congruence.
  - destruct a; auto.
    destruct t0; auto.
    destruct (decide (t=t0)).
    + subst. simpl in *. 
      destruct (decide (t0=t0)); congruence.
    +  simpl in *.
       destruct (decide (t=t0)); try congruence.
       apply IH; easy.
Qed. 

(** Boolean relational version *)

Definition first_loc_forRb 
  (pr: Proc) (t: Term) (l: loc) : bool :=
  match first_loc_for pr t  with
    SomeE l' => beq l l'
  | _ => false
  end.
Global Hint Unfold first_loc_forRb : core.

Lemma  first_loc_forRb_default pr t l :
  first_loc_forRb pr t l = true
  -> first_loc_for_default pr t = l.
Proof.
  intros.
  apply first_loc_for_def_works.
  unfold first_loc_forRb in *.
  destruct (first_loc_for pr t) eqn:eq1.
  destruct (beq_reflect l x).
  - congruence.
  - easy.
  - easy.
Qed.

Lemma first_locR_unique pr t l l' :
  first_loc_forRb pr t l = true ->
  first_loc_forRb pr t l' =true ->
  l = l'.
Proof.
  intros H1 H2.
  unfold first_loc_forRb in *.
  destruct_all_matches. 
  destruct (beq_reflect l x); 
    destruct (beq_reflect l' x); 
    congruence.
Qed.

(* ----------------- *)

(** An indirect definition, easier to show decidable *)

Definition term_is_bound_fl  (pr: Proc)(t: Term) : Prop :=
  exists x, first_loc_for pr t = SomeE x.


Global Instance term_is_bound_fl_dec pr t :
  Decision (term_is_bound_fl pr t).
Proof. 
  hnf.  
  unfold term_is_bound_fl.
  destruct (first_loc_for pr t).
  - left; exists x; easy.
  - right; intros F; destruct F; congruence.
Defined.


Definition term_is_boundb  (pr: Proc)(t: Term) : bool :=
  match first_loc_for pr t with
    NoneE _ => false
  | SomeE _ => true
  end.

(** direct defn, without first_loc.  We get decidability by proving
equivalence with [term_is_bound_fl] *)

Definition term_is_bound pr t : Prop :=
  exists l e, In (Bind (t, l) e) pr.

Lemma term_is_bound_iff pr t :
  term_is_bound_fl pr t <->
    term_is_bound pr t.
Proof.
  unfold term_is_bound_fl, term_is_bound.
  split.
  - intros. destruct H as [v P].
    exists v.
    now apply first_loc_for_elim.
  - intros.
    destruct H as [v [e Q]].
    assert (h:= first_loc_for_intro pr t v e Q).
    destruct h as [v' [e' [Q1 Q2]]].
    exists v'; easy.
Defined.

Global Hint Resolve term_is_bound_iff :core.

Global Instance term_is_bound_dec pr t :
  Decision (term_is_bound pr t).
Proof. 
  apply dec_prop_iff with (term_is_bound_fl pr t).
  auto. apply _.
Defined.

(** useful in reasoning about redexes later *)

Lemma term_bound_extend_proc pr ls trm  :
  term_is_bound pr trm ->
  term_is_bound (pr ++ ls) trm.
Proof.
  intros H.
  unfold term_is_bound in *.
  destruct H as [l [e Q]].
  exists l; exists e; auto.
Qed.


Theorem bound_then_first_loc_for_def (pr: Proc) (t: Term) :
  term_is_bound pr t ->
  exists e, In (Bind (t, (first_loc_for_default pr t)) e) pr.
Proof.
  intros H.
  destruct H as [l [e P]].
  assert (h0:= @first_loc_for_intro pr t l e P).
  destruct h0 as [lf [ef [P1 P2]]].

  assert (h1:= @first_loc_for_def_works pr t lf P2
         ).
  rewrite h1.
  now exists ef.
Qed.

Fixpoint terms_bound_in (pr: Proc) : list Term :=
  match pr with 
    nil =>  nil
  | (Bind (t, _) _) :: rest => 
      t :: (terms_bound_in rest)

  | _ :: rest => terms_bound_in rest 
  end.

Fixpoint term_for_loc
  (pr: Proc)   (l: loc ): optionE Term :=
  match pr with 
    [] => NoneE ("failed term_for: " ++ (show l))
  | (Bind (t, l') e) :: rest => 
      if decide (l = l')
      then SomeE t
      else term_for_loc rest l
  | _ :: rest => term_for_loc rest l
  end.

(** ugly defn but easy to show decidable *)

Definition term_exp_in_proc pr (t: Term) (e: Expr): Prop :=
  exists (s: Stmt), 
    In s pr /\
      match s with
      | Bind (t' , _) e' =>
          t=t' /\ e=e'
      | _ => False
      end.

#[export] Instance term_exp_dec :
  forall pr t e , Decision (term_exp_in_proc pr t e).
Proof.   
  intros.
  (* hnf.  *)
  apply list_exists_dec.
  intros.
  destruct x;
    apply _.
Defined.

(** how to use [term_exp_in_proc] *)

Lemma term_exp_in_proc_elim
  pr (t: Term) (e: Expr) :
  term_exp_in_proc pr t e ->
  exists (l: loc),
    In (Bind (t,l) e) pr.
Proof.
  intros H.
  inv H. destruct x. destruct t0.
  destruct H0 as [H1 [H2 H3] ]; subst.
  exists l; easy.
  all: easy.
Qed.

(** useful in reasoning about redexes later *)

Lemma term_exp_extend_proc pr ls trm exp :
  term_exp_in_proc pr trm exp ->
  term_exp_in_proc (pr ++ ls) trm exp.
Proof.
  intros H.
  apply term_exp_in_proc_elim in H.
  destruct H as [l Q].
  exists (Bind (trm,l) exp); auto.
Qed.


(** Existentially quantify an expression out of a Bind stmt s
 *)
Definition ex_expr_bind (t: Term) (l: loc) (s: Stmt) :=
  exists e, s = Bind (t,l) e.

Global Instance ex_expr_bind_dec :
  forall t l smt, Decision (ex_expr_bind t l  smt).
Proof.  
  intros t l smt.
  destruct smt.
  shelve.  
  all: try (right; intros F; 
            destruct F as [x H]; inv H).
  Unshelve.
  destruct t0.
  destruct (decide (t=t0));
    destruct (decide (l=l0)); subst.
  left.  exists e; easy.
  all: right;
    intros F; destruct F as [x H]; inv H; congruence.
Defined.

Definition binding_in_proc t l pr :=
  exists s, In s pr /\
              exists e, s = (Bind (t,l) e).

Global Instance binding_in_proc_dec t l pr :
  Decision (binding_in_proc t l pr).
Proof.
  hnf; unfold binding_in_proc.
  assert (h:= list_exists_dec pr).
  apply h.
  intros.
  apply ex_expr_bind_dec.
Defined.


Equations binding_in_procb
  (t: Term) (l: loc) (pr: Proc) : bool  :=

  binding_in_procb t l [] := false ;
  
  binding_in_procb t l ((Bind (t1, l1) e) :: rest) := 
    ( (beq t t1) && (beq l l1) )  
    || binding_in_procb t l rest ;

  binding_in_procb t l (x :: rest) :=
    binding_in_procb t l rest .


(** NO WAY this should be this complicated.   Revisit (someday) 
 *)
Lemma reflect_bind t l pr :
  reflect (binding_in_proc t l pr)
    (binding_in_procb t l pr).
Proof.
  intros.
  apply iff_reflect.
  split.
  -  
    intros.
    inv H. destruct H0 as [Hin [e Q]]; subst. clear H.
    induction pr as [| a rest IH] ; auto.
    destruct a; auto; try easy.
    destruct t0; auto; try easy. 
    -- destruct (beq_reflect t0 t);
         destruct (beq_reflect l0 l).
       { subst.
         simp binding_in_procb.  
         do 2 rewrite beq_rfl. now simpl. }
       { (* must have (Bind t l e) in rest *)
         assert (a1: In (Bind (t, l) e) rest).
         { 
           (* simp binding_in_procb. *)
           inv Hin. 
           -- inv H. easy.
           -- easy.
         }
         apply IH in a1.
         simp binding_in_procb in *. 
         apply orb_true_intro; now right.
       }
       
       { (* must have (Bind t l e) in rest *)
         assert (a1: In (Bind (t, l) e) rest).
         { 
           (* simp binding_in_procb. *)
           inv Hin. 
           -- inv H. easy.
           -- easy.
         }
         apply IH in a1.
         simp binding_in_procb in *. 
         apply orb_true_intro; now right.
       }
       {
         (* must have (Bind t l e) in rest *)
         assert (a1: In (Bind (t, l) e) rest).
         { 
           (* simp binding_in_procb. *)
           inv Hin. 
           -- inv H. easy.
           -- easy.
         }
         apply IH in a1.
         simp binding_in_procb in *. 
         apply orb_true_intro; now right.
       }


    -- inv Hin; try easy;
         apply IH in H;
         simp binding_in_procb in *. 
    -- inv Hin; try easy;
         apply IH in H;
         simp binding_in_procb in *. 
    -- inv Hin; try easy;
         apply IH in H;
         simp binding_in_procb in *. 
    -- inv Hin; try easy;
         apply IH in H;
         simp binding_in_procb in *. 
    -- inv Hin; try easy.
       apply IH in H.
       simp binding_in_procb in *. 
    -- inv Hin; try easy.
       apply IH in H.
       simp binding_in_procb in *. 
    -- inv Hin; try easy.
       apply IH in H.
       simp binding_in_procb in *. 


  - 
    apply FunctionalElimination_binding_in_procb ; intros; auto; try easy.
    + apply orb_prop in H0.
      destruct H0 as [H01 | H02].
      apply andb_prop in H01.
      destruct H01 as [H1 H2].

      destruct (beq_reflect t1 t0); subst; auto; subst; try easy;
        destruct (beq_reflect l1 l0); auto; subst; try easy.
      -- exists (Bind (t0,l0) e).
         split.
         ++ auto.

         ++ exists e; auto.

      -- destruct (beq_reflect l0 l1); auto; try easy. congruence.

      -- destruct (beq_reflect t0 t1); auto; try easy. congruence.

      -- destruct (beq_reflect l0 l1); auto; try easy. congruence.

      -- apply H in H02.
         inv H02.  destruct H0 as [Hin [e0 Q]]; subst.
         exists (Bind (t0,l0) e0).
         split. auto. exists e0; auto.

    + apply H in H0;
        inv H0;  destruct H1 as [Hin [e0 Q]]; subst;
        exists (Bind (t0,l0) e0);
        split; auto; exists e0; auto.

    + apply H in H0;
        inv H0;  destruct H1 as [Hin [e0 Q]]; subst;
        exists (Bind (t0,l0) e0);
        split; auto; exists e0; auto.
    + apply H in H0;
        inv H0;  destruct H1 as [Hin [e0 Q]]; subst;
        exists (Bind (t0,l0) e0);
        split; auto; exists e0; auto.
    + apply H in H0;
        inv H0;  destruct H1 as [Hin [e0 Q]]; subst;
        exists (Bind (t0,l0) e0);
        split; auto; exists e0; auto.
    + apply H in H0;
        inv H0;  destruct H1 as [Hin [e0 Q]]; subst;
        exists (Bind (t0,l0) e0);
        split; auto; exists e0; auto.

    + apply H in H0;
        inv H0;  destruct H1 as [Hin [e0 Q]]; subst;
        exists (Bind (t0,l0) e0);
        split; auto; exists e0; auto.

    + apply H in H0;
        inv H0;  destruct H1 as [Hin [e0 Q]]; subst;
        exists (Bind (t0,l0) e0);
        split; auto; exists e0; auto.
Qed.


Lemma get_binding t l pr :
  binding_in_procb t l pr = true ->
  exists e, In (Bind (t,l) e) pr.
Proof.
  destruct (reflect_bind t l pr).
  inv b.
  destruct H as [H1 H2]. 
  destruct H2 as [e Q]; subst.
  now exists e. easy.
Qed.

Lemma get_binding' t l pr :
  binding_in_procb t l pr <> false ->
  exists e, In (Bind (t,l) e) pr.
Proof.
  intros.
  apply (get_binding t l pr).
  destruct (binding_in_procb t l pr) ; easy.
Qed.


Equations binding_in_proc_opt 
  (t: Term) (l: loc) (pr: Proc) : option Expr  :=

  binding_in_proc_opt t l [] := None ;
  
  binding_in_proc_opt t l ((Bind (t1, l1) e) :: rest) := 
    if ( (Term_beq t t1) && (loc_beq l l1) )
    then Some e
    else binding_in_proc_opt t l rest ;

  binding_in_proc_opt t l (x :: rest) :=
    binding_in_proc_opt t l rest .

Definition is_pair_expression_for
  (pr: Proc) (t: Term) (e: Expr) : bool :=
  match (t,e) with
    ((Pr t1 t2), (Pair l1 l2) ) =>
      (binding_in_procb t1 l1 pr) &&
        (binding_in_procb t2 l2 pr)
  | _ => false
  end.

Definition is_encr_expression_for
  (pr: Proc) (t: Term) (e: Expr) : bool :=
  match (t,e) with
    ((En tp tke), (Encr lp lke) ) =>
      (binding_in_procb tp lp pr) && 
        (binding_in_procb tke lke pr)
  | _ => false
  end.

(** aka the compile-time-store *)

Definition tdecl_bound (pr: Proc) (t: Term) (l:loc) : Prop :=
  exists (st: Stmt),
    In st pr /\ 
      match st with
      | Bind (t' , l') _ =>
          t=t' /\ l=l'
      | _ => False
      end.

#[export] Instance tdecl_bound_dec : 
  forall (pr: Proc) (t: Term) (l: loc),
    (Decision (tdecl_bound pr t l )).
Proof. intros pr t l.
       hnf.
       unfold tdecl_bound.
       apply list_exists_dec.
       intros.
       destruct x; apply _.
Defined. 

(* 2023 Mon Jul 10
   A more convenient version of [tdecl_bound]
*)

Inductive tl (pr: Proc) (t: Term) (l: loc) : Prop :=
  tl_1 e: In (Bind (t,l) e) pr ->
          tl pr t l.

Lemma tl_tdecl_iff pr t l :
  tl pr t l <->
    tdecl_bound pr t l.
Proof.
  split.
  - intros.
    inv H. 
    hnf.
    exists (Bind (t,l) e). auto.
  - intros.
    hnf in H. destruct H as [st [H1 H2] ] .
    destruct st. destruct t0. destruct H2; subst.
    apply (tl_1) with  e. auto.
    all: easy.
Qed.


Lemma tdecl_bound_cdr a pr t l :
  tdecl_bound pr t l ->
  tdecl_bound (a::pr) t l.
Proof.
  intros.
  destruct H as [st [P Q] ] .
  exists st.
  split.
  apply in_cons; easy.
  assumption.
Qed.


Lemma first_loc_tdecl pr t l :
first_loc_for pr t = SomeE l ->
tdecl_bound pr t l.
Proof.
  intros H. 
  induction pr as [| a rest IH] .
  - inv H.
  - destruct a; simpl in H.
    + destruct t0 as (t', l').
      destruct (decide (t= t')) eqn:e'.
      -- inv H.
         exists (Bind (t', l) e).
         split; auto. 
      -- specialize (IH H).
         apply tdecl_bound_cdr; easy.
    + (specialize (IH H); apply tdecl_bound_cdr; easy).
    + (specialize (IH H); apply tdecl_bound_cdr; easy).
    + (specialize (IH H); apply tdecl_bound_cdr; easy).
    + (specialize (IH H); apply tdecl_bound_cdr; easy).
    + (specialize (IH H); apply tdecl_bound_cdr; easy).
    + (specialize (IH H); apply tdecl_bound_cdr; easy).
    + (specialize (IH H); apply tdecl_bound_cdr; easy).
Qed.         

(** a sufficient condition for [tdcl_bound] *)

Lemma tdecl_bound_intro
  (pr: Proc) (t: Term) (l: loc) (e: Expr) :
  In (Bind (t,l) e) pr ->
  tdecl_bound pr t l.
Proof.
  intros H.
  unfold tdecl_bound.
  exists (Bind (t,l) e).
  tauto.
Qed.

Lemma tdecl_bound_elim pr t l :
 tdecl_bound pr t l ->
 exists  (e : Expr), In (Bind (t, l) e) pr.
Proof.
  intros H.
  hnf in H.
  destruct H as [st [H1 H2] ]; subst.
  destruct st. 
  { destruct t0. destruct H2; subst.  exists e; auto. }
  all: easy.
Qed.


Lemma tdecl_mono (pr1 pr2 : list Stmt) : 
  subset pr1 pr2 ->
forall t l, 
  tdecl_bound pr1 t l ->
  tdecl_bound pr2 t l .
Proof.
  intros H1 t l H2.
  unfold tdecl_bound in *.
  destruct H2 as [st [P Q] ] .
  exists st.
  split.
  - apply H1; easy.
  - easy.
Qed.


(* ---------------------------------- *)
(** ** Extract the actions in a Proc *)

(** Extract the event Stmts, and strip off the [Evt] constructors 
*)
Fixpoint prtrace
  (pr: Proc) : list (Act loc) :=
  match pr with
    [] => []
  | Evnt alpha :: rest => alpha :: (prtrace rest)
  | _  :: rest => (prtrace rest)
  end.


(** * Taxonomy of Proc statements *)
(* ------------------------------- *)

(* ** Checks *)

Definition is_check (s: Stmt) : bool :=
  match s with
| Csame _ _ => true 
| Ckypr _ _ => true 
| Csrt _ _ => true 
| Cquote _ _ => true 
| _ => false
  end .

Definition checks_of (pr:Proc) : list Stmt :=
  filter (is_check) pr.

(* ** Events *)

Definition is_Evnt  : Stmt -> bool :=
  fun es => match es with
              Evnt _ => true
            | _ => false
            end.

Definition is_non_Evnt  (s: Stmt) : bool :=
  negb (is_Evnt s).


(** The [Evnt]s of a Proc but with the [Evnt] constructor still
attached *)

Definition Evnts_of (pr: Proc) : list Stmt :=
  filter is_Evnt pr.

Definition non_Evnts_of (pr: Proc) : list Stmt :=
  filter is_non_Evnt pr.

Lemma Evnts_of_app pr1 pr2 :
  Evnts_of (pr1 ++ pr2) =
  Evnts_of pr1 ++
  Evnts_of pr2 .
Proof.
  apply filter_app.
Qed.

Lemma non_Evnts_of_app pr1 pr2 :
  non_Evnts_of (pr1 ++ pr2) =
    non_Evnts_of pr1 ++
      non_Evnts_of pr2 .
Proof.
  apply filter_app.
Qed.

(* ** External, events and comments
vs
    Internal; everything else *)

(** The things in the compile-time "store": things OTHER than Evnt and Comm
*)
Definition is_Internal  : Stmt -> bool :=
  fun es => match es with
              Evnt _ => false
            | Comm _ => false
            | _ => false
            end.


Definition Internals_of (pr: Proc) : list Stmt :=
  filter is_Internal pr.

Lemma Internals_app pr1 pr2 :
  Internals_of (pr1 ++ pr2) =
    Internals_of pr1 ++
      Internals_of pr2 .
Proof.
  apply filter_app.
Qed.


Definition is_External  (s: Stmt) : bool :=
  negb (is_Internal s).
Arguments is_External /.

Definition Externals_of (pr: Proc) : list Stmt :=
  filter is_External pr.

Lemma External_app pr1 pr2 :
  Externals_of (pr1 ++ pr2) =
    Externals_of pr1 ++
      Externals_of pr2 .
Proof.
  apply filter_app.
Qed.


(* ---------------------------- *)
(* Pull the action alpha of an stmt of the form [Evt alpha] .  But returns option *)
 

Definition action_of_st (st: Stmt) : option (Act loc) :=
  match st with
  | Evnt alpha => Some alpha
  | _ => None
  end.

 Definition prtrace'
  (pr: Proc) :=
  map_opt action_of_st pr.

(** Two defns of prtace are equivalent ... *)

Lemma prtrace_equiv (pr: Proc) :
  prtrace pr = prtrace' pr.
Proof.
  induction pr; simpl; auto.
  unfold prtrace' in *.
  destruct a; simpl; auto.
  now rewrite  IHpr.
Qed.



(** ** Key pairs in a Proc *)

(** Does k have its inverse named in [pr] ? *)
Definition has_inv_named_in
  (pr: Proc) (k: Term) : Prop :=
  has_inv_in (terms_bound_in pr) k.
(* *)
#[export] Instance has_inv_named_in_dec :
  forall pr k, Decision (has_inv_named_in pr k).
Proof. intros ts k.
       apply _.
Defined.

(* ------------------------------------------------------ *)
(** ** Things about indices for input, read, and generate *)

(** The largest read loc number appearing in ls *)
(** But: initialize with 0, so [fresh_read_index]
    will start with 1.
 *)

Fixpoint max_read_index (pr: Proc) : nat := 
   match pr with
     [] => 0
   | (Bind _ (Read i )) :: rest  => 
        max i (max_read_index rest)
   | _ :: rest => (max_read_index rest)
   end.

Definition fresh_read_index (ls:  Proc) : nat :=
 (S (max_read_index ls)).

(* --------- *)

(** The largest input loc number appearing in ls *)
(** But: initialize with 0, so [fresh_input_index]
    will start with 1.
 *)

Fixpoint max_input_index (pr: Proc) : nat := 
   match pr with
     [] => 0
   | (Bind _ (Param i )) :: rest  => 
        max i (max_input_index rest)
   | _ :: rest => (max_input_index rest)
   end.

Definition fresh_input_index (pr: Proc) : nat :=
 (S (max_input_index pr)).

(* --------- *)

(** The largest Genr index appearing in ls *)
(** But: initialize with 0, so [fresh_gen_index]
    will start with 1.
 *)


Lemma prtrace_app (x y : list Stmt) :
  prtrace (x++y) =
    (prtrace x) ++ (prtrace y).
Proof.
  induction x as [| a rest IH]; simpl; auto.
  destruct a .
  all:  (rewrite  IH; easy).
Qed.
 


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


(** ** Utilities used in Saturation termination *)

Definition size_bind   (s:Stmt) :nat :=
  match s with
    Bind (t,_) _ => size_term t
  | _ => 0
  end.

(** is s an I_binding for t ? *)

Definition is_I_binding_for (t: Term) (s: Stmt) : bool :=
  match s with
  | Bind (t,_) e => is_I_expr e
  | _ => false
  end . 

Definition is_I_binding (s: Stmt) : bool :=
  match s with
  | Bind (_,_) e => is_I_expr e
  | _ => false
  end . 

(** is there an I_binding for t in pr ? *)

Definition is_I_bound (pr: Proc) (t: Term) : bool :=
  existsb (is_I_binding_for t) pr.  

Definition is_not_I_bound (pr: Proc) (t: Term) : bool :=
  negb (is_I_bound pr t) .

(** the terms in unv that are NOT I_bound in pr *)

Definition the_not_I_bound (unv: Terms) (pr: Proc) : Terms :=
  filter (is_not_I_bound pr) unv.


