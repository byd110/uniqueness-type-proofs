Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import ZArith.
Require Import Coq.Arith.Compare_dec.
Require Import Notations Logic Datatypes.
Require Decimal Hexadecimal Number.
Import ListNotations.

Require Import env.
Require Import vars.
Require Import defs.


Import OpeningNotations.
Local Open Scope opening.


Definition heap := list (ty * list (ty * tm)).

Definition store := list (ty * tm).

Definition tenv := list ty.  (* static type env *)  

 (* simplify the constructor to default assignment to every field. *)


(*
Definition obj_rec: (ty * list (ty * tm)).
 *)

Inductive teval: tm -> store  -> heap  -> (ty * tm) -> Prop :=
 | e_true: forall σ h,
    teval ttrue σ h (TBool, ttrue)

 | e_false: forall σ h,
    teval tfalse σ h (TBool, tfalse)

 | e_oid: forall σ h o c object ts,
    indexr o h = Some ((TCls c ts), object) ->
    teval &o σ h (TCls c ts, &o)

 | e_var: forall σ h x v T,
    indexr x σ = Some (T, v) ->
    value v ->
    teval (tvar $x) σ h (T, v) 

 | e_facc: forall σ h x c f fs l T v ts,
    indexr x σ = Some ((TCls c ts), (toid l))->
    indexr l h = Some ((TCls c ts), fs) ->
    indexr f fs = Some(T, v) ->
    value v ->
    teval (tfacc ($x) f) σ h (T, v) 

  | e_oid_facc: forall σ h c f fs oid T v ts,
    indexr oid h = Some ((TCls c ts), fs) ->
    indexr f fs = Some (T, v) ->
    value v ->
    teval (toidfacc oid f)  σ h (T, v)
.

Inductive value_runtime_ty: store -> heap -> class_table -> tm -> ty -> Prop :=
| runtime_ty_true: forall h σ ct,
  value_runtime_ty σ h ct ttrue TBool

| runtime_ty_false: forall σ h ct,
  value_runtime_ty σ h ct tfalse TBool

| runtime_ty_notunique: forall σ h ct c fs l ts,
  c < length ct ->
  indexr l h = Some (TCls c ts, fs) ->
  ts <> TSUnique ->
  value_runtime_ty σ h ct (&l) (TCls c ts)

| runtime_ty_unique: forall σ h ct c fs l,
  c < length ct ->
  indexr l h = Some (TCls c TSUnique, fs) ->
  (exists! x, indexr x σ = Some (TCls c TSUnique, &l)) \/
  ~(exists x, indexr x σ = Some (TCls c TSUnique, &l)) ->
  value_runtime_ty σ h ct (&l) (TCls c TSUnique)
.


Inductive varlist_eval : list var -> store -> heap -> list (ty * tm)-> Prop :=
| vl_nil: forall  σ h,
  varlist_eval [] σ h []
| vl_cons: forall x xs σ h T v vs,
  teval (tvar $x) σ h (T, v)  ->
  varlist_eval xs σ h vs ->
  varlist_eval (($x):: xs) σ h ((T, v)::vs)
.

Inductive tmlist_eval : list tm -> store -> heap -> list (ty * tm)-> Prop :=
| tl_nil: forall  σ h,
  tmlist_eval [] σ h []
| tl_cons: forall t ts σ h T v vs,
  teval t σ h (T, v)  ->
  tmlist_eval ts σ h vs ->
  tmlist_eval (t:: ts) σ h ((T, v)::vs)
.

Inductive object_valid_semantic : list (ty * tm) -> store -> heap -> class_table -> list ty -> Prop := 
| o_nil: forall σ h ct,
  object_valid_semantic [] σ h ct []

| o_cons: forall fs T v o σ h ct,
  value v ->
  value_runtime_ty σ h ct v T ->
  length o = length fs ->
  object_valid_semantic o σ h ct fs ->
  object_valid_semantic ((T, v) :: o) σ h ct (T :: fs)
.

Inductive loop_body : stmt -> nat -> nat -> stmt -> Prop := 
  | loop_begin: forall s l,
  loop_body s 0 l sskip

  | loop_cons: forall s l c s',
  loop_body s c l s'->
  c < l ->
  loop_body s (S c) l (sseq s' s)
.

(*
Fixpoint dvalues (Ts: list ty) : list tm :=
  match Ts with
  | [] => []
  | TBool :: tail => ttrue :: (dvalues tail)
  | (TCls c) :: tail => tnull :: (dvalues tail)
  | _ :: tail => terror :: (dvalues tail)
end.
*)
(*
Fixpoint extract_fields_ty (fds: list field_decl) : list ty :=
  match fds with
  | [] => []
  | (f_decl T) :: tail => T :: (extract_fields_ty tail)
end.
*)


Inductive step: stmt -> store -> heap -> class_table -> store -> heap -> Prop :=
 | step_skip: forall σ h ct,
   step sskip σ h ct σ h    
 
 | step_seq: forall σ h ct s1 s2 σ' h' σ'' h'',
   step s1 σ h ct σ' h' ->  (* this is big step semantics *)
   step s2 σ' h' ct σ'' h'' -> 
   closed_stmt 0 (length σ) s2 ->
   step (sseq s1 s2) σ h ct σ'' h''

 | step_assgnC: forall σ h ct x y v,
   indexr y σ = Some (TBool, v) ->
   value v ->
   x < length σ ->
   step (sassgn $x $y) σ h ct (update σ x (TBool, v)) h 

 | step_assgnU: forall σ h ct x y v c σ',
   indexr y σ = Some (TCls c TSUnique, v) ->
   value v ->
   x < length σ ->
   σ' = update (update σ y (TCls c TSBot, v)) x (TCls c TSUnique, v) ->
   step (sassgn $x $y) σ h ct σ' h 

 | step_assgnS: forall σ h ct x y v c σ',
   indexr y σ = Some (TCls c TSShared, v) ->
   value v ->
   x < length σ ->
   σ' = update σ x (TCls c TSShared, v) ->
   step (sassgn $x $y) σ h ct σ' h 

 | step_load: forall σ h ct x y f c l fs v ts T,
   indexr y σ = Some ((TCls c ts), (toid l)) ->
   indexr l h = Some ((TCls c ts), fs) ->
   indexr f fs = Some (T, v) ->
   value (v) ->
   x < length σ ->
   step (sload $x $y f) σ h ct (update σ x (T, v)) h

 (* | step_loadS: forall σ h ct x y f c c' l fs v ts,
   indexr y σ = Some ((TCls c ts), (toid l)) ->
   indexr l h = Some ((TCls c ts), fs) ->
   indexr f fs = Some (TCls c' TSShared, v) ->
   value (v) ->
   x < length σ ->
   step (sload $x $y f) σ h ct (update σ x (TCls c' TSShared, v)) h *)

 | step_storeC: forall σ h ct x f y v l c fs fs' h' v',
   indexr y σ =  Some (TBool, v) ->
   value v -> 
   indexr x σ =  Some ((TCls c TSShared), (toid l)) ->  
   indexr l h = Some ((TCls c TSShared), fs) ->
   indexr f fs = Some (TBool, v') ->
   fs' = update fs f (TBool, v) ->
   h' = update h l ((TCls c TSShared), fs') -> 
   step (sstore $x f $y) σ h ct σ h'

 | step_storeS: forall σ h ct x f y v l c c' fs fs' h' v',
   indexr y σ =  Some (TCls c' TSShared, v) ->
   value v -> 
   indexr x σ =  Some ((TCls c TSShared), (toid l)) ->  
   indexr l h = Some ((TCls c TSShared), fs) ->
   indexr f fs = Some (TCls c' TSShared, v') ->
   fs' = update fs f (TCls c' TSShared, v) ->
   h' = update h l ((TCls c TSShared), fs') -> 
   step (sstore $x f $y) σ h ct σ h'

 | step_storeU: forall σ h ct x f y o l c c' fs obj fs' h' v' σ',
   indexr y σ =  Some (TCls c' TSUnique, &o) ->
   indexr o h = Some (TCls c' TSUnique, obj) -> 
   indexr x σ =  Some ((TCls c TSShared), (toid l)) ->  
   indexr l h = Some ((TCls c TSShared), fs) ->
   indexr f fs = Some (TCls c' TSShared, v') ->
   fs' = update fs f (TCls c' TSShared, &o) ->
   h' = update (update h o (TCls c' TSShared, obj)) l ((TCls c TSShared), fs') -> 
   σ' = update σ y (TCls c' TSBot, &o) ->
   step (sstore $x f $y) σ h ct σ' h'
   
 | step_mcall: forall σ h ct x y m z c o fl init ml T1 T s t σ' h' ts r,
   indexr y σ = Some ((TCls c ts), &o) ->  (* receiver *)
   indexr c ct = Some (cls_def fl init ml) ->
   indexr m ml = Some (m_decl T1 T s t) ->   (* find the method def in ct*)
   step (s <~ˢ $y; $z) σ h ct σ' h' ->
   teval (t <~ᵗ $y; $z) σ' h' (T, r) ->
   x < length σ ->
   z < length σ ->
   step (smcall $x $y m $z) σ h ct (update σ' x (T, r)) h'  
  
  | step_lettmC: forall σ h ct t r r' T T' s σ' h',
    teval t σ h (T, r) ->
    (* notice here we only consider the case that s has single bound var
    (0 in terms of nameless var). is it like a 1-arg function? is it possible
    that let-binding can have more than one bound var in the stmt? *)
    (forall c, T <> TCls c TSUnique) ->
    step (open_rec_stmt 0 $(S (length σ)) s) ((T, r) :: σ) h ct (((T', r') :: σ')) h' ->
    step (slettm T t s) σ h ct σ' h'

  | step_lettmU: forall σ h ct x r r' T' c s σ' h',
    teval $x σ h (TCls c TSUnique, r) ->
    (* notice here we only consider the case that s has single bound var
    (0 in terms of nameless var). is it like a 1-arg function? is it possible
    that let-binding can have more than one bound var in the stmt? *)
    step (open_rec_stmt 0 $(S (length σ)) s) ((TCls c TSUnique, r) :: (update σ x (TCls c TSBot, r))) h ct (((T', r') :: σ')) h' ->
    step (slettm (TCls c TSUnique) $x s) σ h ct σ' h'
  
  | step_letnew: forall σ σ' h h' ct c ps objrec s v fs init ms ts ts', 
    (* comment below for assumption that we assign same initial value for any constructor args *)
    closed_var_list 0 (length σ) ps ->
    indexr c ct = Some(cls_def fs init ms) ->
    varlist_eval ps σ h objrec ->
    object_valid_semantic objrec σ h ct fs ->
    (* (forall objrec', object_valid_semantic objrec' h ct fs -> objrec = objrec') -> *)
    step (open_rec_stmt 0 $(S (length σ)) s) (((TCls c ts), (&(length h))):: σ) (((TCls c ts), objrec) ::h) ct (((TCls c ts'), v):: σ') h' ->
    step (sletnew (TCls c ts) (TCls c ts) ps s) σ h ct σ' h'                                   
    (* change sletnew TCls c TCls c into sletnew c0 TCls c when adding subtype. *)

  | step_if_true: forall σ h ct x s1 s2 σ' h',
    teval $x σ h (TBool, ttrue) ->
    step  s1 σ h ct σ' h' ->
    closed_stmt 0 (length σ) s2 ->
    step (sif $x s1 s2) σ h ct σ' h'

  | step_if_false: forall σ h ct x s1 s2 σ' h',
    teval $x σ h (TBool, tfalse) ->
    step  s2 σ h ct σ' h' ->
    closed_stmt 0 (length σ) s1 ->
    step (sif $x s1 s2) σ h ct σ' h'  

  | step_loop_true: forall σ h ct x c l s σ' h' s',
    teval $x σ h (TBool, ttrue) -> 
    loop_body s c l s' ->
    step s' σ h ct σ' h' ->
    c < l ->
    (* step (sloop $x (S c) l s) σ' h' ct σ'' h'' -> *)
    step (sloop $x c l s) σ h ct σ' h'  
  
  | step_loop_terminate: forall σ h ct x s c l,
    c >= l ->
    step (sloop $x c l s) σ h ct σ h
  
  | step_loop_false: forall σ h ct x c s l,
    teval $x σ h (TBool, tfalse) -> 
    c < l ->
    (* step s σ h ct σ' h' -> *)
    step (sloop $x c l s) σ h ct σ h

.

Lemma step_extend_store: forall {s σ h ct σ' h'}, step s σ h ct σ' h' -> 
   length σ <= length σ'.
Proof.
   intros. induction H; subst; simpl; try lia. all: try rewrite <- update_length; try lia.
   rewrite <- update_length. auto.
   assert (length ((T, r) :: σ) = S (length σ)) by auto. 
   assert (length ((T, r') :: σ') = S(length (σ'))).
   {
     repeat rewrite app_length. simpl. lia.
   }  all: simpl in IHstep; try rewrite <- update_length in IHstep; lia.
Qed.

Lemma step_extend_heap: forall {s σ h ct σ' h'}, step s σ h ct σ' h' -> 
  length h <= length h'.
Proof.
  intros. induction H; subst; try lia. 1-3: repeat erewrite <- update_length; intuition. 
  assert (length ((TCls c ts, objrec) :: h) = S (length h)) by auto. rewrite H4 in IHstep. lia.
Qed.

(* Lemma step_preserve_heap: forall {s l c object σ h ct σ' h' f T v ts}, step s σ h ct σ' h' -> 
  indexr l h = Some ((TCls c ts), object) -> indexr f object = Some(T, v) -> value v ->
  (exists o' v', indexr l h' = Some ((TCls c ts), o') /\ indexr f o' = Some(T, v') /\ value v').
Proof.
  intros. generalize dependent object. generalize dependent v. induction H. 1,17: intros; exists object, v; auto.
  2, 3, 4, 5: intros; exists object, v0; auto. all: intros. specialize (IHstep1 v). intuition. specialize (H5 object).
  intuition. destruct H5 as [o' [v' H5]]. specialize (IHstep2 v'). intuition. specialize (H7 o'). intuition. 
  1-3: destruct (l =? l0) eqn:E1; destruct (f =? f0) eqn:E2. 1,5,9: exists fs', v; apply Nat.eqb_eq in E1, E2; subst.
  rewrite H7 in H2. inversion H2; subst. rewrite H8 in H3. inversion H3; subst.
  rewrite update_indexr_hit. intuition. rewrite update_indexr_hit; intuition.
  apply indexr_var_some' in H8; auto. apply indexr_var_some' in H7; auto.
  rewrite H7 in H2. inversion H2; subst. rewrite H8 in H3. inversion H3; subst.
  rewrite update_indexr_hit. intuition. rewrite update_indexr_hit; intuition.
  apply indexr_var_some' in H8; auto. apply indexr_var_some' in H7; auto.
  rewrite H8 in H2; inversion H2; subst. rewrite H9 in H3; inversion H3; subst.
  erewrite update_indexr_hit; intuition. erewrite update_indexr_hit; intuition.
  apply indexr_var_some' in H9; auto. apply indexr_var_some' in H8; auto.
  1,4,7: apply Nat.eqb_eq in E1; apply Nat.eqb_neq in E2; exists fs', v0; subst. rewrite H7 in H2.
  inversion H2; subst. rewrite update_indexr_hit. intuition. erewrite update_indexr_miss; eauto.
  apply indexr_var_some' in H7; auto. 
  inversion H2; subst. rewrite update_indexr_hit. intuition. erewrite update_indexr_miss; eauto.
  apply indexr_var_some' in H7; auto. 
  apply Nat.eqb_neq in E1. exists object, v0.
  rewrite H5. rewrite update_indexr_miss; auto. apply Nat.eqb_neq in E1. exists object, v0.
  rewrite H5. rewrite update_indexr_miss; auto. 1,2,4,5: try specialize (IHstep v); intuition. specialize (H9 object); auto.
  specialize (H4 object); auto. specialize (H5 object); auto. specialize (H5 object); auto.
  specialize (IHstep v0). intuition. specialize (H7 object). intuition.
  apply indexr_var_some' in H5 as H5'. assert (l <> length h) by lia.
  eapply indexr_skip in H8. erewrite H8 in H7. intuition. specialize (IHstep v); intuition.
  specialize (H6 object); intuition. exists object, v; intuition.
Qed.

Lemma step_preserve_heap': forall {s l c object σ h ct σ' h' ts}, step s σ h ct σ' h' -> 
  indexr l h = Some ((TCls c ts), object) -> 
  (exists o', indexr l h' = Some ((TCls c ts), o')).
Proof.
  intros. generalize dependent object. induction H; intros. 1,3,4,5,6,14: exists object; auto.
  specialize (IHstep1 object). intuition. destruct H3 as [o' H3]. 
  specialize (IHstep2 o'). intuition. 
  destruct (l =? l0) eqn:E1. exists fs'. apply Nat.eqb_eq in E1; subst. 
  rewrite H6 in H2. inversion H2; subst. rewrite update_indexr_hit. intuition. 
  apply indexr_var_some' in H6; auto. apply Nat.eqb_neq in E1. exists object.
  rewrite H5. rewrite update_indexr_miss; auto. all: try specialize (IHstep object); auto. 
  apply indexr_var_some' in H4 as H5. assert (l <> length h) by lia.
  eapply indexr_skip in H6. erewrite H6 in IHstep. intuition. exists object; intuition. 
Qed. *)

(* Lemma teval_closed: forall  {σ h t T v},  teval t σ h (T, v) ->  closed_tm 0 (length σ) t.
Proof.
  intros. induction H; simpl; eauto.
  + constructor. apply indexr_var_some' in H. auto.
  + constructor. apply indexr_var_some' in H. auto.
Qed.

Lemma step_closed: forall {σ h σ' h' ct s}, step s σ h ct σ' h' -> closed_stmt 0 (length σ) s.
Proof.
  intros. induction H; auto; constructor; auto. 
  all: try apply indexr_var_some' in H; auto; try apply indexr_var_some' in H1; auto;
  try apply teval_closed in H; auto. 
  all: try inversion H; subst; auto. 
Qed. *)

Lemma teval_deterministic: forall {t σ h T v1 v2},
  teval t σ h (T, v1) ->
  teval t σ h (T, v2) ->
  v1 = v2.
Proof.
  intros. inversion H; inversion H0; subst; try discriminate || reflexivity.
  inversion H8; subst. intuition. inversion H10; subst. 
  rewrite H13 in H6. inversion H6; subst. reflexivity.
  inversion H14; subst. rewrite H12 in H3; inversion H3; subst.
  rewrite H13 in H4; inversion H4; subst. rewrite H17 in H8; inversion H8; subst. reflexivity.
  inversion H12; subst. rewrite H11 in H3; inversion H3; subst.
  rewrite H15 in H7; inversion H7; subst. reflexivity.
Qed.  

Lemma varlist_eval_deterministic: forall {xs σ h vs1 vs2},
  varlist_eval xs σ h vs1 ->
  varlist_eval xs σ h vs2 ->
  vs1 = vs2.
Proof.
  intros. generalize dependent vs1; generalize dependent vs2. 
  induction xs; intros. inversion H; inversion H0; subst. reflexivity.
  inversion H; inversion H0; subst.  inversion H8; subst.
  inversion H3; inversion H10; subst. rewrite H9 in H18; inversion H18; subst.
  specialize (IHxs vs). intuition. specialize (H1 vs0). intuition. subst. reflexivity.  
Qed.

Lemma loop_body_deterministic: forall{s c l s' s''},
  loop_body s c l s' ->
  loop_body s c l s'' ->
  s' = s''.
Proof.
  intros. generalize dependent s''. induction H; intros. inversion H0; subst. auto.
  inversion H1; subst. specialize (IHloop_body s'0). intuition; subst; auto.
Qed.


(* the reduction is deterministic process. The same satement will always reduce into
   same result. *)
Lemma step_deterministic: forall {s σ h ct σ' h' σ'' h''},
  step s σ h ct σ' h' ->
  step s σ h ct σ'' h'' ->
  σ' = σ'' /\ h' = h''.
Proof.
  intros. 
  generalize dependent h''. generalize dependent σ''. 
  induction H; intros Hσ Hh H'.   
  (* sskip *)
  - inversion H'; subst. split; reflexivity. 
  (* sseq *)
  - inversion H'; subst.  specialize (IHstep1 σ'0 h'0) as IH1. intuition; subst;
    specialize (IHstep2 Hσ Hh) as IH2; intuition.
  (* sassgnC *)
  - inversion H'; subst; rewrite H4 in H; inversion H; subst. 
    split; reflexivity. 
  (* sassgnU *)
  - inversion H'; subst; rewrite H5 in H; inversion H; subst. 
    split; reflexivity. 
  (* sassgnS *)
  - inversion H'; subst; rewrite H5 in H; inversion H; subst. 
    split; reflexivity. 
  (* sload *)
  - inversion H'; subst. rewrite H7 in H; inversion H; subst.
    rewrite H8 in H0; inversion H0; subst. rewrite H9 in H1; inversion H1; subst.
    split; reflexivity.
  (* sstoreC *)
  - inversion H'; subst; rewrite H9 in H; inversion H; subst.
    rewrite H11 in H1; inversion H1; subst. rewrite H12 in H2; inversion H2; subst.
    rewrite H13 in H3; inversion H3; subst. split; reflexivity.
  (* sstoreS *)
  - inversion H'; subst; rewrite H9 in H; inversion H; subst.
    rewrite H11 in H1; inversion H1; subst. rewrite H12 in H2; inversion H2; subst.
    rewrite H13 in H3; inversion H3; subst. split; reflexivity.
  (* sstoreU *)
  - inversion H'; subst; rewrite H10 in H; inversion H; subst.
    rewrite H12 in H1; inversion H1; subst. rewrite H13 in H2; inversion H2; subst.
    rewrite H14 in H3; inversion H3; subst. rewrite H11 in H0; inversion H0; subst.
    split; reflexivity.
  (* smcall *)
  - inversion H'; subst. rewrite H10 in H; inversion H; subst.
    rewrite H11 in H0; inversion H0; subst. rewrite H12 in H1; inversion H1; subst.
    specialize (IHstep σ'0 Hh). intuition; subst. 
    specialize (teval_deterministic H3 H19) as H22; subst. reflexivity.
  (* slettmC *)
  - inversion H'; subst. specialize (teval_deterministic H H5) as H13; subst.
    specialize (IHstep ((T'0, r'0) :: Hσ) Hh) as H13. intuition. inversion H3; subst.
    auto. inversion H; inversion H10; subst. rewrite H16 in H7; inversion H7; subst.
    specialize (H0 c). contradiction.
  (* slettmU *)
  - inversion H'; subst. inversion H; inversion H4; subst. rewrite H16 in H7; inversion H7; subst.
    specialize (H10 c). contradiction. inversion H; inversion H9; subst. rewrite H15 in H6;
    inversion H6; subst. specialize (teval_deterministic H H9) as H13; subst.
    specialize (IHstep ((T'0, r'0) :: Hσ) Hh) as H14. intuition. inversion H2; subst.
    auto. 
  (* sletnew *)
  - inversion H'; subst. rewrite H16 in H0; inversion H0; subst.
    specialize (varlist_eval_deterministic H1 H17) as Heq. subst.
    intuition; subst. all: specialize (IHstep ((TCls c ts'0, v0) :: Hσ) Hh); intuition.
    inversion H5; auto.
  (* sif true *)
  - inversion H'; subst.
    (* true, true *)
    + specialize (IHstep Hσ Hh) as H13; intuition.
    (* true, false *)
    + specialize (teval_deterministic H H5) as H13. inversion H13.
  (* sif false *)
  - inversion H'; subst.
    (* false, true *)
    + specialize (teval_deterministic H H5) as H13. inversion H13.
    (* false, false *)
    + specialize (IHstep Hσ Hh) as H13; intuition.
  (* sloop true *)
  - inversion H'; subst.
    (* true, true *)
    + specialize (loop_body_deterministic H0 H13) as Heq. subst. 
      specialize (IHstep Hσ Hh). intuition.
    (* true terminate *)
    + lia.
    (* true false *)
    + specialize (teval_deterministic H H12) as H12'. inversion H12'.
  (* sloop terminate *)
  - inversion H'; subst.
    (* terminate, true *)
    + lia.
    (* terminate, terminate *)
    + auto.
    (* terminate, false *)
    + auto.
  (* sloop false *)
  - inversion H'; subst.
    (* false, true *)
    + specialize (teval_deterministic H H5) as H12'. inversion H12'.
    (* false, terminate *)
    + lia.
    (* false, false *)
    + auto.
Qed.
  
Lemma object_valid_hit: forall {object σ h ct fs f T v }, object_valid_semantic object σ h ct fs ->
  indexr f object = Some (T, v) -> (value v /\ value_runtime_ty σ h ct v T /\ indexr f fs = Some T ).
Proof.
  intros. induction H; subst. inversion H0. destruct (f =? length o) eqn: E1. 
  + apply Nat.eqb_eq in E1. subst. rewrite indexr_head in H0. inversion H0; subst. rewrite H2.
    rewrite indexr_head. intuition.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H0; auto. intuition. rewrite H2 in E1.
    rewrite indexr_skip; auto.
Qed.