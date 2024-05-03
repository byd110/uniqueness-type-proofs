Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import ZArith.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import env.
Require Import vars.
Require Import defs.
Require Import semantics.

Import OpeningNotations.
Local Open Scope opening.

Definition heap := list (ty * list (ty * tm)).

Definition store := list (ty * tm).

Definition tenv := list ty.  (* static type env *)  

(* field types *)
Inductive f_has_ty : class_table -> nat (* class name *) -> nat (* field name *) ->  ty  ->  Prop :=
  | ty_f: forall c d ct fl init ml f T, 
    indexr c ct = Some(cls_def d fl init ml) ->
    indexr f fl = Some  T ->
    wf_ty T ct ->
    (* wf_normal_ty T ct -> *)
    f_has_ty ct c f T
.

Inductive intersection: tenv -> tenv -> tenv -> Prop :=
  | inter_nil: intersection [] [] []

  | inter_shared: forall Γ1 Γ2 Γ' c,
    length Γ1 = length Γ2 ->
    intersection Γ1 Γ2 Γ' ->
    intersection ((TCls c TSShared) :: Γ1) ((TCls c TSShared) :: Γ2) ((TCls c TSShared) :: Γ')
  
  | inter_unique: forall Γ1 Γ2 Γ' c,
    length Γ1 = length Γ2 ->
    intersection Γ1 Γ2 Γ' ->
    intersection ((TCls c TSUnique) :: Γ1) ((TCls c TSUnique) :: Γ2) ((TCls c TSUnique) :: Γ')
  
  | inter_bot: forall Γ1 Γ2 Γ' c,
    length Γ1 = length Γ2 ->
    intersection Γ1 Γ2 Γ' ->
    intersection ((TCls c TSBot) :: Γ1) ((TCls c TSBot) :: Γ2) ((TCls c TSBot) :: Γ')
  
  | inter_else: forall Γ1 Γ2 Γ' c ts1 ts2,
    length Γ1 = length Γ2 ->
    intersection Γ1 Γ2 Γ' ->
    ts1 <> ts2 ->
    intersection ((TCls c ts1) :: Γ1) ((TCls c ts2) :: Γ2) ((TCls c TSBot) :: Γ')
.


(* expression types *)
Inductive tm_has_ty: tenv -> class_table -> tm -> ty -> Prop :=
  | ty_tm_true: forall Γ ct,
    tm_has_ty Γ ct ttrue TBool
  
  | ty_tm_false: forall Γ ct,
    tm_has_ty Γ ct tfalse TBool

  | ty_tm_varB: forall Γ ct x,
    indexr x Γ  = Some TBool ->
    tm_has_ty Γ ct $x TBool
  
  (* | ty_tm_varBot: forall Γ ct x c,
    indexr x Γ  = Some (TCls c TSBot)  ->
    tm_has_ty Γ ct $x (TCls c TSBot) *)

  | ty_tm_varC: forall Γ ct x c ts ,
    indexr x Γ  = Some (TCls c ts) ->
    ts <> TSBot ->
    wf_ty (TCls c ts) ct ->
    tm_has_ty Γ ct $x (TCls c ts)
  
  | ty_tm_facc: forall Γ ct x c f T ts ,
    wf_ty T ct ->
    c < length ct ->
    tm_has_ty Γ ct $x (TCls c ts) ->
    wf_ty (TCls c ts) ct ->
    f_has_ty ct c f T ->
    tm_has_ty Γ ct (tfacc $x f) T

  | ty_tm_sub: forall Γ ct t T U,
    tm_has_ty Γ ct t T ->
    T <: U ~ ct ->
    (forall c ts, U = TCls c ts -> ts <> TSBot) ->
    tm_has_ty Γ ct t U

  (* | ty_tm_oid: forall Γ h ct l c object,
    c < length ct ->
    indexr l h = Some ((TCls c), object) ->
    l < length h ->
    tm_has_ty Γ h ct (& l) (TCls c) 
  
  | ty_tm_oid_facc: forall Γ h ct c oid f fvlues T v,
    c < length ct ->
    indexr oid h = Some ((TCls c), fvlues) ->
    indexr f fvlues = Some (T, v) ->
    value v ->
    tm_has_ty Γ h ct v T ->
    tm_has_ty Γ h ct (toidfacc oid f) T *)
.


(* constructor's parameter list types *)

Inductive parameter_has_ty : tenv -> class_table -> list var -> list ty -> Prop :=
 | ty_parameter_nil: forall Γ ct,
   parameter_has_ty Γ ct [] []

 | ty_parameter_cons: forall Γ ct x xs T Ts,
   tm_has_ty Γ ct $x T ->
   parameter_has_ty Γ ct xs Ts ->
   parameter_has_ty Γ ct (($x)::xs) (T::Ts)
.


(* statements types *)
Inductive stmt_has_ty: tenv -> class_table -> stmt -> tenv -> Prop :=
  | ty_stmt_skip : forall Γ ct,
    stmt_has_ty Γ ct sskip Γ

  | ty_stmt_assgnC: forall Γ ct x y,
    tm_has_ty Γ ct $x TBool ->
    tm_has_ty Γ ct $y TBool ->
    stmt_has_ty Γ ct (sassgn $x $y) Γ
    
  | ty_stmt_assgnU: forall Γ ct x y c ts Γ',
    tm_has_ty Γ ct $x (TCls c ts) ->
    tm_has_ty Γ ct $y (TCls c TSUnique) ->
    Γ' = update (update Γ y (TCls c TSBot)) x (TCls c TSUnique) ->
    stmt_has_ty Γ ct (sassgn $x $y) Γ'

  | ty_stmt_assgnS: forall Γ ct x y c ts Γ',
    tm_has_ty Γ ct $x (TCls c ts) ->
    tm_has_ty Γ ct $y (TCls c TSShared) ->
    Γ' = update Γ x (TCls c TSShared) ->
    stmt_has_ty Γ ct (sassgn $x $y) Γ'

  | ty_stmt_loadC: forall Γ ct x y f,
    tm_has_ty Γ ct $x TBool ->
    tm_has_ty Γ ct (tfacc $y f) TBool ->
    stmt_has_ty Γ ct (sload $x $y f) Γ

  | ty_stmt_loadS: forall Γ Γ' ct x y f c ts,
    tm_has_ty Γ ct $x (TCls c ts) ->
    tm_has_ty Γ ct (tfacc $y f) (TCls c TSShared) ->
    Γ' = update Γ x (TCls c TSShared) ->
    stmt_has_ty Γ ct (sload $x $y f) Γ'

  | ty_stmt_storeC: forall Γ ct x y f c,
    tm_has_ty Γ ct $x (TCls c TSShared) ->
    tm_has_ty Γ ct (tfacc $x f) TBool ->
    tm_has_ty Γ ct $y TBool ->
    stmt_has_ty Γ ct (sstore $x f $y) Γ

  | ty_stmt_storeS: forall Γ ct x y f c c',
    tm_has_ty Γ ct $x (TCls c TSShared) ->
    tm_has_ty Γ ct (tfacc $x f) (TCls c' TSShared) ->
    tm_has_ty Γ ct $y (TCls c' TSShared) ->
    stmt_has_ty Γ ct (sstore $x f $y) Γ

  | ty_stmt_storeU: forall Γ ct x y f c c' Γ',
    tm_has_ty Γ ct $x (TCls c TSShared) ->
    tm_has_ty Γ ct (tfacc $x f) (TCls c' TSShared) ->
    tm_has_ty Γ ct $y (TCls c' TSUnique) ->
    Γ' = update Γ y (TCls c' TSBot) ->
    stmt_has_ty Γ ct (sstore $x f $y) Γ'

  | ty_stmt_mcallC: forall Γ Γ' ct c d x y z m s t Tp fs init ms ts,    (* x := y.m (z) *)
    tm_has_ty Γ ct $x TBool ->
    tm_has_ty Γ ct $y (TCls c ts) ->
    indexr c ct = Some(cls_def d fs init ms) ->
    indexr m ms = Some (m_decl Tp TBool s t) ->
    tm_has_ty Γ' ct (t <~ᵗ $y; $z) TBool ->
    tm_has_ty Γ' ct $x TBool ->
    stmt_has_ty Γ ct (s <~ˢ $y; $z) Γ' ->
    tm_has_ty Γ ct $z Tp -> (* only one parameter here, change it to para_has_ty in the future. *)
    stmt_has_ty Γ ct (smcall $x $y m $z) Γ'

  | ty_stmt_mcallS: forall Γ Γ' ct c d c' x y z m s t Tp fs init ms ts ts' ts'',    (* x := y.m (z) *)
    tm_has_ty Γ ct $x (TCls c' ts') ->
    tm_has_ty Γ ct $y (TCls c ts) ->
    indexr c ct = Some(cls_def d fs init ms) ->
    indexr m ms = Some (m_decl Tp (TCls c' TSShared) s t) ->
    tm_has_ty Γ' ct (t <~ᵗ $y; $z) (TCls c' TSShared) ->
    tm_has_ty Γ' ct $x (TCls c' ts'') ->
    stmt_has_ty Γ ct (s <~ˢ $y; $z) Γ' ->
    tm_has_ty Γ ct $z Tp -> (* only one parameter here, change it to para_has_ty in the future. *)
    stmt_has_ty Γ ct (smcall $x $y m $z) (update Γ' x (TCls c' TSShared))

  | ty_stmt_mcallU: forall Γ Γ' ct c d c' x tx y z m s t Tp fs init ms ts ts' ts'',    (* x := y.m (z) *)
    tm_has_ty Γ ct $x (TCls c' ts') ->
    tm_has_ty Γ ct $y (TCls c ts) ->
    indexr c ct = Some(cls_def d fs init ms) ->
    indexr m ms = Some (m_decl Tp (TCls c' TSUnique) s t) ->
    tm_has_ty Γ' ct (t <~ᵗ $y; $z) (TCls c' TSUnique) ->
    tm_has_ty Γ' ct $x (TCls c' ts'') ->
    stmt_has_ty Γ ct (s <~ˢ $y; $z) Γ' ->
    tm_has_ty Γ ct $z Tp -> (* only one parameter here, change it to para_has_ty in the future. *)
    t <~ᵗ $y; $z = $tx ->
    stmt_has_ty Γ ct (smcall $x $y m $z) (update (update Γ' tx (TCls c' TSBot)) x (TCls c' TSUnique))

  | ty_stmt_slettmC: forall Γ Γ' ct t T1 T1' s,       (* var x : T2 = t in S *)  (* bound variable is implicit *)
    closed_stmt 1 (length Γ) s ->
    tm_has_ty Γ ct t T1 ->
    (forall c, T1 <> TCls c TSUnique) ->
    stmt_has_ty (T1::Γ) ct (open_rec_stmt 0 $(S (length Γ)) s) (T1' :: Γ') ->
    stmt_has_ty Γ ct (slettm T1 t s) Γ'

  | ty_stmt_slettmU: forall Γ Γ' ct x c s T1',       (* var x : T2 = t in S *)  (* bound variable is implicit *)
    closed_stmt 1 (length Γ) s ->
    tm_has_ty Γ ct $x (TCls c TSUnique) ->
    (* teval t σ h (T1, v) ->
    tm_has_ty Γ σ h ct v T1 -> (* consider use tm_safety *)
    value v -> (* try to eliminate these two lines by proving the progress property of term. *) *)
    stmt_has_ty ((TCls c TSUnique)::(update Γ x (TCls c TSBot))) ct (open_rec_stmt 0 $(S (length Γ)) s) (T1' :: Γ') ->
    stmt_has_ty Γ ct (slettm (TCls c TSUnique) $x s) Γ'

  | ty_stmt_sletnew: forall Γ Γ' ct c d ps Ts s this s0 fs ms init ts ts',    (* var x : C2 = new C1 in S *) 
                                                       (* var x : C = new C(ps) in S *)
    indexr c ct = Some(cls_def d fs init ms) ->
    init = init_decl Ts s0 this ->
    closed_stmt 1 (length Γ) s ->
    closed_var_list 0 (length Γ) ps ->
    parameter_has_ty Γ ct ps fs ->
    stmt_has_ty ((TCls c ts)::Γ) ct (open_rec_stmt 0 $(S (length Γ)) s) ((TCls c ts')::Γ') -> 
    stmt_has_ty Γ ct (sletnew (TCls c ts) (TCls c ts) ps s) Γ'
  
  | ty_stmt_sif: forall Γ Γ' ct x s1 s2,   
    tm_has_ty Γ ct $x TBool ->
    stmt_has_ty Γ ct s1 Γ' -> 
    stmt_has_ty Γ ct s2 Γ' ->
    stmt_has_ty Γ ct (sif $x s1 s2) Γ'

  | ty_stmt_sloop: forall Γ ct x c l s s',   
    tm_has_ty Γ ct $x TBool ->
    loop_body s c l s' ->
    stmt_has_ty Γ ct s' Γ->
    c < l ->
    closed_stmt 0 (length Γ) s ->
    stmt_has_ty Γ ct (sloop $x c l s) Γ
 
  | ty_stmt_sseq: forall Γ Γ1 Γ2 ct s1 s2 ,
    stmt_has_ty Γ ct s1 Γ1 ->
    (* step s1 σ h ct σ' h' -> *)
    stmt_has_ty Γ1 ct s2 Γ2 ->
    closed_stmt 0 (length Γ) s2 ->
    (* stmt_has_ty Γ σ' h' ct s2 -> *)
    (* should we also modify Γ so it can remain identical to the store 
    since we need this property in StoreOK? *)
    stmt_has_ty Γ ct (sseq s1 s2) Γ2
.


(* type-check method body *)
Inductive m_has_ty:class_table -> nat (* class name *) -> nat (* method name *) -> Prop :=
  | ty_m: forall ct c d m fl init ml Tr Tp t s ts Γ,              (* implicit (lambda ret. s; t) t1 *)
    indexr c ct  = Some(cls_def d fl init ml) ->
    indexr m ml = Some(m_decl Tp Tr s t) ->
    stmt_has_ty (Tr :: Tp :: [(TCls c ts)]) ct s Γ ->
    tm_has_ty (Tr :: Tp :: [(TCls c ts)]) ct t Tr ->
    m_has_ty ct c m
.


Lemma tm_has_ty_closed: forall  {Γ ct t T },  tm_has_ty Γ ct t T ->  closed_tm 0 (length Γ) t.
Proof. intros. induction H; auto.
      + constructor. apply indexr_var_some' in H. auto.
      + constructor. apply indexr_var_some' in H. auto.
      (* + constructor. apply indexr_var_some' in H. auto. *)
      + constructor. inversion IHtm_has_ty; subst. auto.
Qed.


Lemma stmt_has_ty_closed: forall  {Γ Γ' ct s},  stmt_has_ty Γ ct s Γ' ->  closed_stmt 0 (length Γ) s.
Proof. intros. induction H; auto; constructor; auto.
       all: try apply tm_has_ty_closed in H; inversion H; subst; auto;
       try apply tm_has_ty_closed in H0; inversion H0; subst; auto;
       try apply tm_has_ty_closed in H1; inversion H1; subst; auto;
       try apply tm_has_ty_closed in H6; inversion H6; subst; auto. 
Qed.


Lemma f_ty_inversion: forall {ct c f T}, wf_ct ct -> f_has_ty ct c f T -> 
      exists d fl init ml, indexr c ct = Some (cls_def d fl init ml) 
              /\ indexr f fl = Some T.
Proof. intros. induction H0. 
       + exists d, fl, init, ml.  intuition.
Qed.

Lemma tfacc_type_inversion: forall {Γ ct x f T}, wf_ct ct -> tm_has_ty Γ ct (tfacc $ x f) T -> 
  exists c U, c < length ct -> (f_has_ty ct c f U /\ U <: T ~ ct).
Proof. intros. remember (tfacc $ x f) as t. induction H0; inversion Heqt; subst.
       exists c, T; intuition. intuition. destruct H5 as [c [U' H5]]. exists c, U'; intuition.
       econstructor; eauto.  
Qed.


(* Lemma obj_type_inversion: forall {Γ h ct l c}, tm_has_ty Γ h ct (& l) (TCls c) -> 
  exists object, indexr l h = Some ((TCls c), object) /\ l < length h.
Proof. intros. inversion H. subst. exists object. auto.
Qed. *)

Lemma tbool_inversion: forall {Γ ct v}, (value v) -> tm_has_ty Γ ct v TBool -> 
           (v = ttrue \/ v = tfalse).
Proof. intros. induction H0; intuition.
       all: inversion H.
Qed.

Lemma sub_var_inversion: forall {Γ ct x T}, tm_has_ty Γ ct $x T -> 
  (exists U, indexr x Γ = Some U /\ tm_has_ty Γ ct $x U /\
   U <: T ~ ct /\ wf_ty U ct).
Proof.
  intros. remember (tvar $x) as t. induction H; inversion Heqt; subst.
  assert (tm_has_ty Γ ct $x TBool). econstructor; eauto. exists TBool; auto.
  assert (tm_has_ty Γ ct $x (TCls c ts)). econstructor; eauto. exists (TCls c ts); auto.
  intuition. destruct H3 as [U' H3]. exists U'. intuition. econstructor; eauto.
Qed.

Lemma sub_ts_not_bot: forall {Γ ct t c ts}, wf_ct ct -> tm_has_ty Γ ct t (TCls c ts) ->
  ts <> TSBot.
Proof.
  intros. remember (TCls c ts) as T. generalize dependent ts. generalize dependent c.
  induction H0; intros; inversion HeqT; subst. auto. inversion H4; subst. 
  specialize (wf_ct_to_Tf_shared H H6 H7) as Hts. subst. discriminate. 
  specialize (H2 c ts); intuition.
Qed.

Lemma sub_facc_inversion: forall {Γ ct x f T}, tm_has_ty Γ ct (tfacc $ x f) T ->
  (exists U c ts, tm_has_ty Γ ct $x (TCls c ts) /\ f_has_ty ct c f U /\ U <: T ~ ct).
Proof.
  intros. remember (tfacc $ x f) as t. induction H; inversion Heqt; subst.
  exists T, c, ts. intuition. intuition. destruct H3 as [U' [c [ts H3]]].
  exists U', c, ts. intuition. econstructor; eauto. 
Qed.

(* Lemma sub_f_has_ty: forall {ct c c' f T ts}, f_has_ty ct c f T -> (TCls c' ts) <: (TCls c ts) ~ ct ->
  f_has_ty ct c' f T.
Proof.
  intros. remember (TCls c' ts) as T1; remember (TCls c ts) as T2. induction H0. 
  rewrite HeqT1 in HeqT2; inversion HeqT2; subst; auto. 
  specialize (sub_cls_inversion H2) as Heq.
  destruct Heq as [c'' Heq]; subst. *)

(* Lemma type_preserve_base: forall {Γ ct x s c ts Γ'}, tm_has_ty Γ ct $x (TCls c ts) -> stmt_has_ty Γ ct s Γ' ->
  (exists ts', tm_has_ty Γ' ct $x (TCls c ts')).
Proof.
  intros. induction H0; intuition.
  + exists ts; auto.
  + exists ts; auto.
  + destruct (x =? x0) eqn: E1.
    - apply Nat.eqb_eq in E1; subst. exists TSUnique. inversion H0; subst. econstructor; eauto.
      all: inversion H; subst; rewrite H10 in H7; inversion H7; subst.
      rewrite update_indexr_hit; auto. rewrite <- update_length; apply indexr_var_some' in H10; auto.
      discriminate. inversion H1; subst; auto.
    - apply Nat.eqb_neq in E1. destruct (x =? y) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. exists TSBot. inversion H1; inversion H0; subst.
        econstructor; eauto. *)

(* Lemma tm_store_irre: forall {Γ σ h ct t T}, 
  tm_has_ty Γ σ h ct t T -> 
  forall σ', tm_has_ty Γ σ' h ct t T.
Proof. 
  intros. induction H; subst; econstructor; eauto.
Qed. *)

(* Lemma type_to_semantic: forall{objrec Γ ct fs}, object_valid_type objrec Γ ct fs ->
  object_valid_semantic objrec fs.
Proof.
  intros. induction H. constructor. constructor; auto.
Qed. *)

(* Lemma tm_preservasion: forall {Γ s σ h ct t T σ' h'},
  tm_has_ty Γ σ h ct t T -> step s σ h ct σ' h' ->
  tm_has_ty Γ σ' h' ct t T.
Proof.
  intros. induction H0; subst; auto. 1,2,4: eapply tm_store_irre; eauto. 
  inversion H; subst. 1-4: econstructor; eauto. destruct (l =? l0) eqn:E1.
  apply Nat.eqb_eq in E1; subst. econstructor; eauto. erewrite update_indexr_hit; eauto.
  rewrite H6 in H3. inversion H3; subst. eauto. erewrite <- update_length. 
  eapply indexr_var_some'; eauto. apply Nat.eqb_neq in E1. econstructor; eauto.
  erewrite update_indexr_miss; eauto. erewrite <- update_length. eapply indexr_var_some'; eauto.
Admitted. *)

(* Lemma object_valid_hit: forall {object Γ ct fs f T v }, object_valid_type object Γ ct fs ->
  indexr f object = Some (T, v) -> (value v /\ tm_has_ty Γ ct v T /\ indexr f fs = Some T ).
Proof.
  intros. induction H; subst. inversion H0. destruct (f =? length o) eqn: E1. 
  + apply Nat.eqb_eq in E1. subst. rewrite indexr_head in H0. inversion H0; subst. rewrite H2.
    rewrite indexr_head. intuition.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H0; auto. intuition. rewrite H2 in E1.
    rewrite indexr_skip; auto.
Qed. *)

(* Lemma toidfacc_store_irre: forall {Γ σ h ct oid f Tf}, 
  tm_has_ty Γ σ h ct (toidfacc oid f) Tf -> 
  forall σ', tm_has_ty Γ σ' h ct (toidfacc oid f) Tf.
Proof. intros. inversion H. subst. econstructor; eauto. 
  eapply tm_store_irre; eauto.
Qed. *)


(* Lemma para_store_irre: forall {Γ σ h ct p T},
parameter_has_ty Γ σ h ct p T -> 
  forall σ', parameter_has_ty Γ σ' h ct p T.
Proof.
  intros. induction H; subst; econstructor; try eapply tm_store_irre; eauto.
Qed. *)

(* Lemma stmt_store_irre: forall {Γ σ h ct s T Tv v}, 
  stmt_has_ty Γ σ h ct s T -> 
  stmt_has_ty Γ ((Tv,v) :: σ) h ct s T.
Proof.
  intros. induction H; subst; econstructor; try eapply tm_store_irre;
  try eapply para_store_irre; eauto.
Admitted. *)


(* Lemma teval_has_type: forall {Γ σ h ct t v T}, 
  teval t σ h (T, v) -> 
  tm_has_ty Γ σ h ct v T /\ value v.
Proof.
  intros. inversion H; subst; auto; intuition; try econstructor; eauto.
  admit. apply indexr_var_some' in H4. auto. inversion H6; subst.  


  inversion H9; subst. assert (tm_has_ty Γ σ h ct ttrue TBool). { constructor. }
Admitted. *)




(*
Lemma test: forall {Γ σ h ct x v T},
  indexr x σ = Some (T, v) -> value v -> tm_has_ty Γ σ h ct v T.
Proof. intros. induction v.
   + admit.
   + admit.
   + admit.
   + inversion H0.
   + admit.
   + inversion H0. 
*)
