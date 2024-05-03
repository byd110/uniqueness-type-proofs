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
Require Import type.
Require Import semantics.

Import OpeningNotations.
Local Open Scope opening.

(* remove subtyping *)
(* put it into different defs *)
(* lemmas derived from ctxok *)

(* Forall var in tenv, it must also in store with same index and type.
   And the type of var is a class, the value must be a object in the heap*)
(* Definition StoreOK (Γ: tenv)(σ: store)(h: heap)(ct: class_table) : Prop :=
   length Γ = length σ /\ wf_ct ct /\
   forall x Tx, indexr x Γ = Some Tx -> 
   exists vx, indexr x σ = Some (Tx, vx) /\ (value vx)  /\ 
    tm_has_ty Γ ct vx Tx  /\ 

    (forall c, Tx = (TCls c) -> (exists l fvalues, l < length h /\ vx = &l /\ 
    indexr l h = Some ((TCls c), fvalues) ))  
. *)

Definition StoreOK (Γ: tenv)(σ: store)(h: heap)(ct: class_table) : Prop :=
   length Γ = length σ /\ wf_ct ct /\
   forall x Tx, indexr x Γ = Some (Tx) ->
   ((exists c vx, Tx = TCls c TSBot /\ indexr x σ = Some (TCls c TSBot, vx)) \/
   (exists vx, indexr x σ = Some (Tx, vx) /\ (value vx)  /\ 
    value_runtime_ty σ h ct vx Tx /\ tm_has_ty Γ ct $x Tx /\

    (forall c ts, Tx = (TCls c ts) -> (exists l fvalues, l < length h /\ vx = &l /\ 
    indexr l h = Some ((TCls c ts), fvalues) ))))
.

Lemma StoreOK_wf_ct: forall {Γ σ h ct}, StoreOK Γ σ h ct -> wf_ct ct.
Proof. intros. inversion H. intuition.
Qed.

(* 
Lemma CtxOK_ttrue: forall {Γ σ h ct x}, StoreOK Γ σ h ct -> 
     indexr x Γ = Some TBool -> (indexr x σ = Some (TBool, ttrue) \/ indexr x σ = Some (TBool, tfalse)).
Proof. intros Γ σ h ct x HStore. apply StoreOK_wf_ct in HStore as H'; intuition.
       assert (tm_has_ty Γ σ h ct $x TBool). { econstructor; auto.  } 
       inversion HStore. intuition.
       specialize (H4 x TBool). intuition. 
       destruct H2 as [vx H2']. intuition.
       specialize (tbool_inversion H5 H2). intuition. subst. left. auto. subst. right. auto.
Qed. *)


(* two properties of heap: 
    1.forall oid, oid < length h -> exists c object, indexr oid h = Some (TCls c, object) ->
      (forall f, f < length object -> exists T v, indexr f object = Some (T, v) /\ 
      value v /\ tm_has_ty Γ σ h ct v T ) 
    2.HeapOK below. *)

(* For every class type var that is valid in store, the class it belongs to 
   must have corresponding def in class_table. And for every field in the def,
   the heap must record the same type of it as decleared in the def.*)
(* Definition HeapOK (Γ: tenv)(σ: store)(h: heap)(ct: class_table) : Prop :=
   forall x c, indexr x Γ = Some (TCls c) -> 
           (*value &oid /\ *)   (* ClsOK Γ σ h ct c oid*)
   ( exists fl init ml oid,
          indexr x σ = Some ((TCls c), &oid)/\
          indexr c ct = Some (cls_def fl init ml) /\ 
            (forall f Tf, indexr f fl = Some Tf -> 
                (exists vf object,
                        indexr oid h = Some ((TCls c), object) /\ 
                        indexr f object = (Some (Tf, vf)) /\  (value vf) /\
                        tm_has_ty Γ ct (tfacc $x f) Tf /\
                        tm_has_ty Γ ct vf Tf)
                        (*the conjunction before is the def of this term*)
            )
   )      
.   *)

Definition HeapOK (Γ: tenv)(σ: store)(h: heap)(ct: class_table) : Prop :=
   forall x c ts, tm_has_ty Γ ct $x (TCls c ts) -> 
           (*value &oid /\ *)   (* ClsOK Γ σ h ct c oid*)
   ( exists c' d fl init ml oid,
          indexr x σ = Some ((TCls c' ts), &oid)/\
          indexr c' ct = Some (cls_def d fl init ml) /\ 
          (TCls c' ts) <: (TCls c ts) ~ ct /\
            (forall f Tf, indexr f fl = Some Tf -> 
                (exists vf object,
                        indexr oid h = Some ((TCls c' ts), object) /\ 
                        indexr f object = (Some (Tf, vf)) /\  (value vf) /\
                        tm_has_ty Γ ct (tfacc $x f) Tf /\
                        value_runtime_ty σ h ct vf Tf)
                        (*the conjunction before is the def of this term*)
            )
   )      
.

Definition HeapOK' (Γ: tenv)(σ: store)(h: heap)(ct: class_table) : Prop :=
  forall o c ts object, indexr o h = Some (TCls c ts, object) -> 
    (exists d fl init ml, indexr c ct = Some (cls_def d fl init ml) /\ length fl = length object /\ 
    (forall f , f < length object -> (exists T v, indexr f object = Some (T, v) /\ 
      value v /\ value_runtime_ty σ h ct v T /\ indexr f fl = Some T)))
.

(* Definition ClsOK (Γ: tenv)(σ: store)(h: heap)(ct: class_table)(c: cn)(oid: l) : Prop := 
  exists fl init ml, 
  indexr c ct = Some (cls_def fl init ml) /\ 
    (forall f Tf, indexr f fl = Some Tf /\ 
        (exists vf object,
                indexr oid h = Some ((TCls c), object) /\ 
                indexr f object = (Some (Tf, vf)) /\  (value vf) /\
                tm_has_ty Γ σ h ct (toidfacc oid f) Tf)). *)

(* Fixpoint HeapOK *)

Definition CtxOK (Γ: tenv)(σ: store)(h: heap)(ct: class_table) : Prop :=
   StoreOK Γ σ h ct /\ HeapOK Γ σ h ct /\ HeapOK' Γ σ h ct
.

Lemma CtxOK_wf_ct: forall {Γ σ h ct}, CtxOK Γ σ h ct -> wf_ct ct.
Proof. intros. inversion H. inversion H0. intuition.
Qed. 


Lemma CtxOK_var_value: forall {Γ σ h ct x T}, CtxOK Γ σ h ct -> tm_has_ty Γ ct $x T -> 
  exists U v, indexr x σ = Some (U, v) /\ value v /\ 
  value_runtime_ty σ h ct v U /\ U <: T ~ ct.
Proof. 
  intros. inversion H. inversion H1. intuition. 
  specialize (sub_var_inversion H0) as Hty. destruct Hty as [U Hty].
  specialize (H7 x U). intuition. specialize (StoreOK_wf_ct H1) as Hwf.
  destruct H7 as [c [vx H7]]; intuition; subst. 
  specialize (sub_cls_inversion_reverse H8) as Hty. destruct Hty as [c' Hty]. 
  rewrite Hty in *. specialize (sub_ts_not_bot Hwf H0) as Heq. contradiction.
  destruct H7 as [vx H4']; intuition; exists U, vx; intuition.
Qed.

(* added *)
Lemma weakening_tm: forall {Γ ct t T Tv}, tm_has_ty Γ ct t T -> 
  tm_has_ty (Tv :: Γ) ct t T.
Proof.
  intros. induction H. 
  + constructor. 
  + constructor. 
  + econstructor; eauto. apply indexr_var_some' in H as H'. assert (indexr x (Tv :: Γ) = indexr x Γ). 
    { apply indexr_skip. lia. } rewrite H0. auto. 
  + econstructor. auto. eauto. assert (indexr x (Tv :: Γ) = indexr x Γ). 
    { apply indexr_var_some' in H as H'. apply indexr_skip. lia. } rewrite H2; eauto. all: auto.
  + econstructor; eauto.
  + econstructor; eauto.
Qed.

Lemma weakening_tm_runtime: forall {σ h ct v T objrec fs c ts}, object_valid_semantic objrec σ h ct fs ->
  value_runtime_ty σ h ct v T ->
  value v ->
  value_runtime_ty σ ((TCls c ts, objrec) :: h) ct v T.
Proof.
  intros. induction H0. 1-3: try econstructor; eauto. 2: eapply runtime_ty_unique; eauto. 
  1,2: rewrite indexr_skip; eauto; apply indexr_var_some' in H2; lia.
  econstructor; eauto.
Qed.

Lemma weakening_tm_runtime_store_TBool: forall {σ h ct v v' T},
  value_runtime_ty σ h ct v T ->
  value_runtime_ty σ h ct v' TBool ->
  value_runtime_ty ((TBool, v') :: σ) h ct v T.
Proof.
  intros. induction H. 1,2,3,5: econstructor; eauto. 
  eapply runtime_ty_unique; eauto. destruct H2. 
  + left. destruct H2. exists x. unfold unique in *.
    intuition. erewrite indexr_skip; eauto. specialize (indexr_var_some' H3) as Heq.
    lia. specialize (H4 x'). destruct (x' =? length σ) eqn: E1. 
    apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H2; auto. inversion H2.
    rewrite indexr_skip in H2; auto. apply Nat.eqb_neq in E1; auto.
  + right. unfold not in *. intros. destruct H3. destruct (x =? length σ) eqn:E1.
    - apply Nat.eqb_eq in E1; subst. erewrite indexr_head in H3. inversion H3.
    - apply Nat.eqb_neq in E1. erewrite indexr_skip in H3; eauto.
Qed.




(* added *)
(* Lemma update_keep_type: forall { Γ σ h ct vx x0 T v}, tm_has_ty Γ σ h ct v T ->
  value vx -> tm_has_ty Γ (update σ x0 (T, vx)) h ct v T.
Proof.
  intros. induction H.
  + constructor.
  + constructor.
  + constructor; auto.
  + econstructor; eauto.
  + econstructor; eauto. destruct (Nat.eqb l x0) eqn: Heq.
    * apply Nat.eqb_eq in Heq. subst. eapply update_indexr_hit; eauto. 
      apply indexr_var_some' in H4. auto.
    * apply Nat.eqb_neq in Heq.  *)

Lemma var_type_safety: forall {Γ σ h ct x T}, 
    CtxOK Γ σ h ct -> tm_has_ty Γ ct $x T ->  
    exists U v, value v /\ indexr x σ = Some (U, v) /\ teval (tvar $x) σ h (U, v) /\ 
    value_runtime_ty σ h ct v U /\ U <: T ~ ct.
Proof. intros Γ σ h ct x T HCT HT. inversion HT; subst.
       1,2: specialize (CtxOK_var_value HCT HT); intuition;
       destruct H as [U [v' H']]; exists U, v'; intuition; constructor; auto.
       specialize (CtxOK_var_value HCT HT). intuition.
       destruct H2 as [U [v' H']]. exists U, v'. intuition. constructor; auto.
Qed.

Lemma var_obj_type_safety: forall {Γ σ h ct x c ts}, 
    CtxOK Γ σ h ct -> tm_has_ty Γ ct $x (TCls c ts) ->  
    exists c' l, value (&l) /\ indexr x σ = Some ((TCls c' ts), &l) /\ 
    teval (tvar $x) σ h ((TCls c' ts), (&l)) /\ (TCls c' ts) <: (TCls c ts) ~ ct.
Proof. intros Γ σ h ct x c ts HCT HT. specialize (tm_has_ty_closed HT) as Hcl.
       inversion HT; subst; inversion HCT.
       inversion H. intuition. 
       specialize (H8 x (TCls c ts)). intuition.
       destruct H8 as [c' [vx H8]]. intuition. inversion H2; subst. contradiction.
       destruct H8 as [vx H4']. intuition.
       specialize (H12 c ts). intuition. destruct H11 as [l [fvalues H8']]. intuition.
       subst. exists c, l. intuition. constructor; auto.
       specialize (sub_var_inversion HT) as Hty. destruct Hty as [U Hty].
       intuition. specialize (sub_cls_inversion H6) as Hsub. destruct Hsub as [c' Hsub];
       subst. inversion H2; intuition. specialize (H12 x (TCls c' ts)). intuition.
       destruct H12 as [c'' [vx H12]]. specialize (sub_ts_not_bot H11 HT). intuition.
       inversion H13; subst. contradiction.
       destruct H12 as [vx H12]. intuition. specialize (H16 c' ts). intuition.
       destruct H15 as [l [fvalues H15]]. intuition; subst. exists c', l.
       intuition. econstructor; eauto. 
  Qed.
  
Lemma field_acc_type_safety: forall {Γ σ h ct T x f}, 
    CtxOK Γ σ h ct -> tm_has_ty Γ ct (tfacc $x f) T ->  
    exists U v, value v /\ teval (tfacc $x f) σ h (U, v) /\ 
    value_runtime_ty σ h ct v U /\ U <: T ~ ct.
Proof. intros Γ σ h ct T x f HCT HT.
       apply CtxOK_wf_ct in HCT as HCT'.
       specialize (tm_has_ty_closed HT) as Hcl.
       specialize (sub_facc_inversion HT) as Hty. 
       destruct Hty as [U [c [ts Hty]]]. intuition.
       specialize (var_obj_type_safety HCT H). intuition.
       destruct H0 as [c' [oid H0']].
       (* apply f_ty_inversion in H9; auto.
       destruct H9 as [fl [init [ml H9']]].  *)
       inversion HCT; intuition. 
       specialize (H6 x c ts). intuition. 
       destruct H8 as [c'' [d [fl [init [ml [oid' H5']]]]]]. intuition.
       rewrite H6 in H3; inversion H3; subst.
       specialize (H12 f U). 
       inversion H1; subst. 
       rewrite H13 in H12; inversion H12; subst.
       intuition. destruct H17 as [vf [object H15']]. intuition.
       exists T, vf; intuition. econstructor; eauto.
       specialize (sub_facc_inversion HT) as Hty.
       destruct Hty as [U [c [ts Hty]]]. intuition.
       specialize (var_obj_type_safety HCT H2). intuition.
       destruct H3 as [c' [oid H0']]. inversion HCT; intuition.
       specialize (H9 x c ts). intuition.
       destruct H11 as [c'' [d [fl [init [ml [oid' H11]]]]]]. intuition.
       specialize (H15 f U). inversion H4; subst. rewrite H14 in H11;
       inversion H11; subst. intuition. destruct H18 as [vf [object H18]].
       exists U, vf. intuition. econstructor; eauto.
Qed.

Lemma term_type_safety: forall {t Γ σ h ct T}, 
    CtxOK Γ σ h ct -> tm_has_ty Γ ct t T -> 
    value t \/  exists U v, value v /\ teval t σ h (U, v) /\ 
    value_runtime_ty σ h ct v U /\ U <: T ~ ct.
Proof. intros t Γ σ h ct T HCT HT. specialize (tm_has_ty_closed HT) as Hcl.
       induction HT; intros; subst.
    + (* tture *) left. auto.
    + (* tfalse *) left. auto.
    + (* $x *) right. assert (tm_has_ty Γ ct ($x) TBool). econstructor; eauto.
      specialize (CtxOK_var_value HCT H0). intuition.
      destruct H1 as [U [v H1']]. intuition. exists U, v. intuition. constructor; auto.
    + right. assert (tm_has_ty Γ ct ($x) (TCls c ts)). econstructor; eauto.
      specialize (CtxOK_var_value HCT H2). intuition. destruct H3 as [U [v H3]].
      intuition. exists U, v. intuition. econstructor; eauto.
    (* + right. specialize (CtxOK_var_value HCT HT). intuition. destruct H3.
      intuition. exists x0. intuition. econstructor; eauto. *)
    + (* x.f *) right. 
      assert (tm_has_ty Γ ct (tfacc $x f) T). { econstructor; eauto. }
      specialize (field_acc_type_safety HCT H3). intuition. 
    (* + left. constructor.
    + right. exists v; intuition. econstructor; eauto. *)
    + (* sub *)
      intuition. right. destruct H1 as [U' [v H1]]. exists U', v. 
      intuition. econstructor; eauto.
Qed.

Lemma term_type_safety': forall {t Γ σ h ct T}, 
  CtxOK Γ σ h ct -> tm_has_ty Γ ct t T -> 
  exists U v, value v /\ teval t σ h (U, v) /\ 
  value_runtime_ty σ h ct v U /\ U <: T ~ ct.
Proof. intros t Γ σ h ct T HCT HT. specialize (tm_has_ty_closed HT) as Hcl.
  induction HT; intros; subst.
  + (* tture *) exists TBool, ttrue. intuition; econstructor; eauto.
  + (* tfalse *) exists TBool, tfalse. intuition; econstructor; eauto.
  + (* $x *) assert (tm_has_ty Γ ct ($x) TBool). econstructor; eauto.
    specialize (CtxOK_var_value HCT H0). intuition.
    destruct H1 as [U [v H1']]. intuition. exists U, v. intuition. constructor; auto.
  + assert (tm_has_ty Γ ct ($x) (TCls c ts)). econstructor; eauto.
    specialize (CtxOK_var_value HCT H2). intuition.
    destruct H3 as [U [v H1']]. intuition. exists U, v. intuition. constructor; auto.
  (* + specialize (CtxOK_var_value HCT H). intuition.
    destruct H0 as [v H1']. intuition. exists v. intuition. constructor; auto. *)
  + (* x.f *)  
    assert (tm_has_ty Γ ct (tfacc $x f) T). { econstructor; eauto. }
    specialize (field_acc_type_safety HCT H3). intuition.
  + (* sub *)
    intuition. destruct H2 as [U' [v H2]]. exists U', v. intuition. econstructor; eauto.
Qed. 

Lemma termlist_type_safety: forall {Γ σ h ct ps Ts}, 
  CtxOK Γ σ h ct -> parameter_has_ty Γ ct ps Ts -> 
  exists objrec, varlist_eval ps σ h objrec /\ object_valid_semantic objrec σ h ct Ts.
Proof.
  intros. induction H0. exists []. intuition. econstructor. econstructor.
  intuition. destruct H2 as [obj H2]. specialize (term_type_safety' H H0) as H3.
  destruct H3 as [U [v H3]]. intuition. exists ((U, v) :: obj). intuition;
  econstructor; eauto. induction H5. auto. simpl. lia.
Qed.

(* Lemma store_ext_runtime: forall {σ h ct v}, value_runtime_ty σ h ct v TBool ->
  value_runtime_ty ((TBool, v) :: σ) h ct v TBool *)


Lemma StoreOK_ext_TBool: forall {Γ σ h ct}, StoreOK Γ σ h ct ->
  forall {v}, value_runtime_ty σ h ct v TBool -> value v -> 
  StoreOK (TBool::Γ) ((TBool, v)::σ) h ct.
Proof. intros. unfold StoreOK in *. split. simpl. lia. intuition.
      destruct (Nat.eqb x (length σ)) eqn: Heqx.
    + rewrite <- H2 in Heqx. apply Nat.eqb_eq in Heqx. subst. right. 
      rewrite indexr_head in H3. inversion H3; subst. exists v. intuition. 
      rewrite H2; rewrite indexr_head; auto. specialize (rt_bool_inversion H0) as Heq.
      intuition; subst; econstructor. econstructor; eauto.
      rewrite indexr_head; auto. inversion H5.
    + apply Nat.eqb_neq in Heqx. erewrite indexr_skip; eauto. rewrite <- H2 in Heqx.  
      specialize (H4 x Tx). rewrite indexr_skip in H3; auto. intuition.
      right. destruct H4 as [vx H4]. exists vx. intuition. 
      eapply weakening_tm_runtime_store_TBool; eauto.
      eapply weakening_tm; eauto. 
Qed.

Lemma HeapOK_ext_TBool: forall {Γ σ h ct}, StoreOK Γ σ h ct ->  HeapOK Γ σ h ct -> HeapOK' Γ σ h ct ->
  forall {v}, value_runtime_ty σ h ct v TBool -> value v -> 
  HeapOK (TBool::Γ) ((TBool, v)::σ) h ct.
Proof. intros. unfold HeapOK in *; intros. specialize (sub_var_inversion H4) as Hty.
      destruct Hty as [U Hty]. intuition. specialize (sub_cls_inversion H6) as Heq.
      destruct Heq as [c' Heq]. subst.
      destruct (Nat.eqb x (length Γ)) eqn: Heqx.
      (* devide into x = length Γ or x != length Γ *)
    + apply Nat.eqb_eq in Heqx. subst. rewrite indexr_head in H5. inversion H5. 
    + apply Nat.eqb_neq in Heqx. eapply indexr_skip in Heqx. rewrite Heqx in H5.
      intuition. specialize (H0 x c' ts). assert (tm_has_ty Γ ct $ x (TCls c' ts)).
      specialize (StoreOK_wf_ct H) as Hwf. specialize (sub_ts_not_bot Hwf H7) as Hts.
      econstructor; eauto. intuition. destruct H10 as [c'' [d [fl [init [ml [oid H10]]]]]].
      intuition. destruct (Nat.eqb x (length σ)) eqn: heqx. 
      (* when x != length Γ, then
      devide into x = length σ or x != length σ *)
      - apply Nat.eqb_eq in heqx. assert (indexr x σ = None). { rewrite indexr_var_none. lia. }
        rewrite H12 in H0. inversion H0.
      - apply Nat.eqb_neq in heqx.  eapply indexr_skip in heqx.
        exists c'', d, fl, init, ml, oid. intuition. erewrite heqx. eauto.
        specialize (H13 f Tf). intuition. 
        destruct H9 as [vf [fvalues H9]]. exists vf, fvalues. intuition.
        eapply weakening_tm; eauto. eapply weakening_tm_runtime_store_TBool; eauto.
Qed.


Lemma CtxOK_ext_TBool: forall {Γ σ h ct}, CtxOK Γ σ h ct ->
  forall {v}, value_runtime_ty σ h ct v TBool -> value v -> 
  CtxOK (TBool::Γ) ((TBool, v)::σ) h ct.
Proof. intros. unfold CtxOK in *; intuition. 
       eapply StoreOK_ext_TBool; eauto.
       eapply HeapOK_ext_TBool; eauto.
       unfold HeapOK' in *. intros. specialize (H4 o c ts object). intuition. 
       destruct H5 as [fl [init [ml H6]]]. intuition. exists fl, init, ml. intuition.
       specialize (H7 f). intuition. destruct H8 as [T [v' H8]]. 
       exists T, v'. intuition. eapply weakening_tm_runtime_store_TBool; eauto.
Qed.

Lemma StoreOK_ext: forall {Γ σ h ct T v}, CtxOK Γ σ h ct ->
  value_runtime_ty σ h ct v T -> value v -> (forall c : cn, T <> TCls c TSUnique) ->
  StoreOK (T::Γ) ((T, v)::σ) h ct.
Proof. 
  intros. inversion H. unfold StoreOK in *. intuition. simpl. lia. 
  destruct (x =? length Γ) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H6; auto. inversion H6; subst. 
    inversion H0; subst.  
    - right. exists ttrue. rewrite H5. rewrite indexr_head; auto. intuition. econstructor; eauto.
      econstructor; eauto. rewrite <- H5; rewrite indexr_head; auto. inversion H9.
    - right. exists tfalse. rewrite H5. rewrite indexr_head; auto. intuition. econstructor; eauto.
      econstructor; eauto. rewrite <- H5; rewrite indexr_head; auto. inversion H9.
    - induction ts. contradiction. right. exists & l. intuition. rewrite H5.
      rewrite indexr_head; auto. inversion H0; subst; econstructor; eauto.
      econstructor; eauto. rewrite indexr_head; auto. discriminate.
      inversion H0; subst. eapply indexr_var_some in H18; eauto. destruct H18; eauto.
      inversion H12; subst. exists l, fs. intuition. apply indexr_var_some' in H10; auto.
      left. exists c, &l. intuition. rewrite H5. rewrite indexr_head; auto.
    - specialize (H2 c). contradiction.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H6; auto. specialize (H8 x Tx).
    intuition. 
    - left. destruct H8 as [c' [v' H8]]. exists c', v'. intuition. rewrite indexr_skip; auto.
      rewrite <- H5; auto.
    - right. destruct H8 as [vx H8]. exists vx. intuition. rewrite indexr_skip; auto.
      rewrite <- H5; auto. 2: inversion H11; econstructor; eauto; rewrite indexr_skip; auto.
      inversion H10; subst. 1-3: econstructor; eauto. eapply runtime_ty_unique; eauto.
      intuition.
      * destruct H16. left. exists x0. unfold unique in *. intuition. specialize (H17 x).
        intuition; subst. rewrite indexr_skip; auto. rewrite H5 in E1; auto.
        destruct (x' =? length σ) eqn: E2.
        ++ apply Nat.eqb_eq in E2; subst. rewrite indexr_head in H15. inversion H15; subst.
           specialize (H2 c). contradiction.
        ++ apply Nat.eqb_neq in E2. rewrite indexr_skip in H15; auto.
      * right. intros. destruct H15. destruct (x0 =? length σ) eqn: E2.
        ++ apply Nat.eqb_eq in E2; subst. rewrite indexr_head in H15. inversion H15; subst.
           specialize (H2 c). contradiction.
        ++ apply Nat.eqb_neq in E2. rewrite indexr_skip in H15. 2: rewrite <- H5; eauto. 
           assert (exists x : nat, indexr x σ = Some (TCls c TSUnique, & l)).
           exists x0; auto. apply H16 in H17; auto.
Qed. 

Lemma HeapOK_ext: forall {Γ σ h ct T v}, CtxOK Γ σ h ct ->
  value_runtime_ty σ h ct v T -> value v -> (forall c : cn, T <> TCls c TSUnique) ->
  HeapOK (T::Γ) ((T, v)::σ) h ct.
Proof. 
  intros. inversion H. intuition. unfold HeapOK in *; intros.  intuition.
  destruct (Nat.eqb x (length Γ)) eqn: Heqx.
  + apply Nat.eqb_eq in Heqx. specialize (H5 x c ts). subst. inversion H4; subst.
    rewrite indexr_head in H12. inversion H12; subst.
    assert (ts = TSShared). induction ts; auto. specialize(H2 c). contradiction.
    contradiction. subst. inversion H0; subst.
    specialize (CtxOK_wf_ct H) as H7. specialize (wf_hit H7 H9) as H8.
    destruct H8 as [init [fl [ml H8]]]. exists fl, init, ml, l. intuition.
    inversion H3. rewrite H10. rewrite indexr_head; auto.
    unfold HeapOK' in H6. specialize (H6 l c TSShared fs). intuition.
    destruct H11 as [fl' [init' [ml' H11]]]. intuition. rewrite H6 in H8.
    inversion H8; subst. apply indexr_var_some' in H10 as H10'. rewrite H11 in H10'.
    specialize (H16 f). intuition. destruct H15 as [T [v H15]]. intuition.
    rewrite H10 in H21. inversion H21; subst. exists v, fs. intuition.
    induction H15. 1,2: inversion H19; subst; econstructor; eauto; econstructor; eauto. 
    inversion H19; subst. eapply ty_tm_facc with (c:= c); eauto. apply indexr_var_some in H20. 
    destruct H20; eauto. econstructor; eauto. apply indexr_var_some in H20; auto. 
    destruct H20; econstructor; eauto. specialize (StoreOK_wf_ct H3) as Hwf.
    specialize (wf_ct_to_Tf_ts Hwf H6 H10) as Heq. contradiction.
    inversion H19; subst. 1-3: econstructor; eauto. specialize (StoreOK_wf_ct H3) as Hwf.
    specialize (wf_ct_to_Tf_ts Hwf H6 H10) as Heq. contradiction.
  + apply Nat.eqb_neq in Heqx. inversion H3. rewrite H7 in Heqx.
    eapply indexr_skip in Heqx as Heqx1. erewrite Heqx1 in *. 
    assert (tm_has_ty Γ ct $ x (TCls c ts)). rewrite <- H7 in Heqx. inversion H4; subst.
    rewrite indexr_skip in H14; eauto. econstructor; eauto. 
    specialize (H5 x c ts). intuition. destruct H8 as [fl [init [ml [oid H8]]]].
    exists fl, init, ml, oid. intuition. specialize (H13 f Tf). intuition.
    destruct H14 as [vf [object H14]]. exists vf, object; intuition.
    eapply weakening_tm; eauto. inversion H18; subst. 1-3: econstructor; eauto.
    eapply runtime_ty_unique; eauto. intuition.
    - left. destruct H21. exists x0. unfold unique in *. intuition.
      apply indexr_var_some' in H21 as H21'. rewrite indexr_skip; auto. lia.
      destruct (x' =? length σ) eqn:E1.
      * apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H20; auto.
        inversion H20; subst. specialize (H2 c0); auto. contradiction.
      * apply Nat.eqb_neq in E1. rewrite indexr_skip in H20; auto.
    - right. intros. destruct H20. destruct (x0 =? length σ) eqn: E1.
      * apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H20; auto.
        inversion H20; subst. specialize (H2 c0); auto.
      * apply Nat.eqb_neq in E1. rewrite indexr_skip in H20; auto.
        assert (exists x : nat, indexr x σ = Some (TCls c0 TSUnique, & l)).
        exists x0. auto. apply H21 in H22; auto. 
  Unshelve. all: auto.
Qed. 

Lemma HeapOK'_ext: forall {Γ σ h ct T v}, CtxOK Γ σ h ct ->
  value_runtime_ty σ h ct v T -> value v -> (forall c : cn, T <> TCls c TSUnique) ->
  HeapOK' (T::Γ) ((T, v)::σ) h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK' in *. intuition.
  specialize (H6 o c ts object). intuition. destruct H7 as [fl [init [ml H7]]].
  exists fl, init, ml. intuition. specialize (H9 f). intuition. destruct H10 as [T' [v' H10]].
  exists T', v'. intuition. inversion H11; subst. 1-3: econstructor; eauto.
  specialize (StoreOK_wf_ct H3) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H6 H13) as Heq.
  contradiction.
Qed.

Lemma CtxOK_ext: forall {Γ σ h ct T v}, CtxOK Γ σ h ct ->
  value_runtime_ty σ h ct v T -> value v -> (forall c : cn, T <> TCls c TSUnique) ->
  CtxOK (T::Γ) ((T, v)::σ) h ct.
Proof. 
  intros. unfold CtxOK; intuition. 
  eapply StoreOK_ext; eauto.
  eapply HeapOK_ext; eauto.
  eapply HeapOK'_ext; eauto.
Qed. 

Lemma StoreOK_ext_unique: forall {Γ σ h ct y c v}, CtxOK Γ σ h ct ->
  teval $ y σ h (TCls c TSUnique, v) ->
  value_runtime_ty σ h ct v (TCls c TSUnique) ->
  tm_has_ty Γ ct $y (TCls c TSUnique) ->
  StoreOK ((TCls c TSUnique)::(update Γ y (TCls c TSBot))) ((TCls c TSUnique, v) :: (update σ y (TCls c TSBot, v))) h ct.
Proof.
  intros. inversion H. unfold StoreOK in *. intuition. simpl. repeat rewrite <- update_length. lia.
  destruct (x =? length Γ) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. assert (length Γ = length (update Γ y (TCls c TSBot))). rewrite <- update_length; auto.
    rewrite H9 in *. rewrite indexr_head in H6. inversion H6; subst. right. 
    assert (length (update Γ y (TCls c TSBot)) = length (update σ y (TCls c TSBot, v))).
    repeat rewrite <- update_length. lia. exists v. intuition. rewrite H10. rewrite indexr_head; auto.
    1,2,4: inversion H1; subst. 1,3,5: contradiction. auto. eapply runtime_ty_unique; eauto. 1: { intuition. 
    - left. exists (length (update σ y (TCls c TSBot, & l))). destruct H11. unfold unique in *.
      intuition. all: inversion H0; subst; specialize (H15 y) as Heq; intuition; subst. rewrite indexr_head.
      auto. destruct (x' =? (length (update σ y (TCls c TSBot, & l)))) eqn: E2.
      * apply Nat.eqb_eq in E2; subst; auto.
      * apply Nat.eqb_neq in E2. rewrite indexr_skip in H11; auto. destruct (x' =? y) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. rewrite update_indexr_hit in H11; auto. inversion H11.
           apply indexr_var_some' in H14; auto.
        ++ apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H11; auto.
           specialize (H15 x'); intuition.
    - inversion H0; subst. assert (exists x : nat, indexr x σ = Some (TCls c TSUnique, & l)).
      exists y; auto. apply H11 in H14; auto. }
    exists l, fs. intuition. 1,3: apply indexr_var_some' in H14; auto. 1,2: inversion H11; subst; auto.
    econstructor; eauto. rewrite indexr_head; auto. discriminate. inversion H2; subst; auto.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H6. destruct (x =? y) eqn: E2.
    - apply Nat.eqb_eq in E2; subst. left. rewrite update_indexr_hit in H6; auto. inversion H6; subst.
      exists c, v. intuition. rewrite indexr_skip; auto. rewrite update_indexr_hit; auto.
      inversion H0; subst. apply indexr_var_some' in H14; auto. rewrite <- update_length.
      rewrite H5 in E1; auto. inversion H2; subst. apply indexr_var_some' in H14; auto.
    - apply Nat.eqb_neq in E2. specialize (H8 x Tx). rewrite update_indexr_miss in H6; auto.
      intuition. 
* left. destruct H8 as [c' [v' H8]]. exists c', v'. intuition. rewrite indexr_skip.
        rewrite update_indexr_miss; auto. rewrite <- update_length. apply indexr_var_some' in H10; lia.
      * right. destruct H8 as [vx H8]. exists vx. intuition. rewrite indexr_skip. rewrite update_indexr_miss;
        auto. rewrite <- update_length. apply indexr_var_some' in H9; lia. inversion H10; subst.
        1-3: econstructor; eauto. eapply runtime_ty_unique; eauto. intuition.
        ++ left. destruct H16. exists x0. unfold unique in *. intuition. all: specialize (H17 x) as Heq;
        intuition; subst. rewrite indexr_skip. rewrite update_indexr_miss; auto. rewrite <- update_length.
        apply indexr_var_some' in H16; lia. destruct (x' =? length (update σ y (TCls c TSBot, v))) eqn: E3.
          -- apply Nat.eqb_eq in E3; subst. rewrite indexr_head in H15; auto. inversion H15; subst.
            inversion H0; subst. specialize (H17 y); intuition.
          -- apply Nat.eqb_neq in E3. destruct (x' =? y) eqn: E4.
            ** apply Nat.eqb_eq in E4; subst. rewrite indexr_skip in H15; eauto. rewrite update_indexr_hit in H15;
                auto. inversion H15. inversion H0; subst. apply indexr_var_some' in H23; auto.
            ** apply Nat.eqb_neq in E4. rewrite indexr_skip in H15; auto. rewrite update_indexr_miss in H15; auto.
        ++ right. intro. destruct H15. destruct (x0 =? length (update σ y (TCls c TSBot, v))) eqn: E3.
           -- apply Nat.eqb_eq in E3; subst. rewrite indexr_head in H15; auto. inversion H15; subst.
              inversion H0; subst. assert (exists x : nat, indexr x σ = Some (TCls c0 TSUnique, & l)).
              exists y. auto. apply H16 in H17; auto.
           -- apply Nat.eqb_neq in E3. destruct (x0 =? y) eqn: E4.
              ** apply Nat.eqb_eq in E4; subst. rewrite indexr_skip in H15; auto. 
                 erewrite update_indexr_hit in H15; eauto. inversion H0; subst. apply indexr_var_some' in H22; auto.
              ** apply Nat.eqb_neq in E4. rewrite indexr_skip in H15; auto.
                 erewrite update_indexr_miss in H15; auto.
                 assert (exists x : nat, indexr x σ = Some (TCls c0 TSUnique, & l)). exists x0.
                 auto. apply H16 in H17; intuition.
        ++ inversion H11; subst. all: econstructor; eauto. all: rewrite indexr_skip.
           1,3: erewrite update_indexr_miss; auto. all: rewrite <- update_length; auto.
    - rewrite <- update_length; auto.
Qed.

Lemma HeapOK_ext_unique: forall {Γ σ h ct y c v}, CtxOK Γ σ h ct ->
  teval $ y σ h (TCls c TSUnique, v) ->
  value_runtime_ty σ h ct v (TCls c TSUnique) ->
  tm_has_ty Γ ct $y (TCls c TSUnique) ->
  HeapOK ((TCls c TSUnique)::(update Γ y (TCls c TSBot))) ((TCls c TSUnique, v) :: (update σ y (TCls c TSBot, v))) h ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK in *. intuition. destruct (x =? length (update Γ y (TCls c TSBot))) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. specialize (H5 y c TSUnique). intuition. destruct H7 as [fl [init [ml [l H7]]]].
    intuition. inversion H0; subst. rewrite H14 in H5; inversion H5; subst. exists fl, init, ml, l.
    assert (length (update Γ y (TCls c TSBot)) = length (update σ y (TCls c TSBot, & l))).
    repeat rewrite <- update_length. inversion H3. auto.
    inversion H4; subst. rewrite indexr_head in H17; auto. inversion H17; subst.
    intuition. rewrite H8. rewrite indexr_head; auto. specialize (H9 f Tf). intuition.
    destruct H11 as [vf [object H11]]. intuition. inversion H1; subst. contradiction.
    rewrite H26 in H9; inversion H9; subst. intuition. 2:{ 
    assert (exists x : nat, indexr x σ = Some (TCls c0 TSUnique, & l)). exists y. intuition.
    apply H16 in H21; intuition. } exists vf, object. intuition. inversion H13; subst.
    econstructor; eauto. inversion H27; inversion H2; subst. rewrite H41 in H33; 
    inversion H33; subst. econstructor; eauto. rewrite indexr_head; auto.
    inversion H20; subst. 1-3: econstructor; eauto. specialize (StoreOK_wf_ct H3) as Hwf.
    specialize (wf_ct_to_Tf_ts Hwf H7 H10) as Heq. contradiction.
  + apply Nat.eqb_neq in E1. destruct (x =? y) eqn: E2.
    - apply Nat.eqb_eq in E2; subst. specialize (H5 y c TSUnique). intuition.
      destruct H7 as [fl [init [ml [l H7]]]]. inversion H4; subst.
      rewrite indexr_skip in H12; auto. rewrite update_indexr_hit in H12; auto. 
      2: { intuition. apply indexr_var_some' in H5. inversion H3. rewrite H8. auto. } 
      inversion H12; subst. intuition. 
    - apply Nat.eqb_neq in E2. specialize (H5 x c0 ts). assert (tm_has_ty Γ ct $ x (TCls c0 ts)).
      inversion H4; subst. rewrite indexr_skip in H12; auto. rewrite update_indexr_miss in H12; auto.
      econstructor; eauto. intuition. destruct H8 as [fl [init [ml [l H8]]]]. exists fl, init, ml, l.
      intuition. rewrite indexr_skip; auto. rewrite update_indexr_miss; auto. rewrite <- update_length.
      rewrite <- update_length in E1. inversion H3. erewrite H9 in E1; auto.
      specialize (H10 f Tf). intuition. destruct H11 as [vf [object H11]]. exists vf, object.
      intuition. inversion H13; subst. econstructor; eauto. inversion H19; subst.
      econstructor; eauto. rewrite indexr_skip; auto. rewrite update_indexr_miss; auto.
      inversion H15; subst. 1-3: econstructor; eauto. specialize (StoreOK_wf_ct H3) as Hwf.
      specialize (wf_ct_to_Tf_ts Hwf H8 H9) as Heq. contradiction.
Qed.


Lemma HeapOK'_ext_unique: forall {Γ σ h ct y c v}, CtxOK Γ σ h ct ->
  teval $ y σ h (TCls c TSUnique, v) ->
  value_runtime_ty σ h ct v (TCls c TSUnique) ->
  tm_has_ty Γ ct $y (TCls c TSUnique) ->
  HeapOK' ((TCls c TSUnique)::(update Γ y (TCls c TSBot))) ((TCls c TSUnique, v) :: (update σ y (TCls c TSBot, v))) h ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK' in *. intros. specialize (H6 o c0 ts object).
  intuition. destruct H7 as [fl [init [ml H7]]]. exists fl, init, ml. intuition.
  specialize (H9 f). intuition. destruct H10 as [T' [v' H10]]. exists T', v'. intuition.
  inversion H11; subst. 1-3: econstructor; eauto. specialize (StoreOK_wf_ct H3) as Hwf.
  specialize (wf_ct_to_Tf_ts Hwf H6 H13) as Heq. contradiction.
Qed.

Lemma CtxOK_ext_unique: forall {Γ σ h ct y c v}, CtxOK Γ σ h ct ->
  teval $ y σ h (TCls c TSUnique, v) ->
  value_runtime_ty σ h ct v (TCls c TSUnique) ->
  tm_has_ty Γ ct $y (TCls c TSUnique) ->
  CtxOK ((TCls c TSUnique)::(update Γ y (TCls c TSBot))) ((TCls c TSUnique, v) :: (update σ y (TCls c TSBot, v))) h ct.
Proof.
  intros. unfold CtxOK. intuition. eapply StoreOK_ext_unique; eauto. eapply HeapOK_ext_unique; eauto.
  eapply HeapOK'_ext_unique; eauto.
Qed.

Lemma StoreOK_ext_unique_pure: forall {Γ σ h ct c obj}, CtxOK Γ σ h ct ->
  CtxOK Γ σ ((TCls c TSUnique, obj) :: h) ct ->
  StoreOK ((TCls c TSUnique) :: Γ) ((TCls c TSUnique, &(length h)) :: σ) ((TCls c TSUnique, obj) :: h) ct.
Proof.
  intros. inversion H; intuition. unfold StoreOK in *. intuition. simpl. lia.
  destruct (x =? length Γ) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. right. rewrite indexr_head in H5. inversion H5; subst.
    inversion H0; intuition. unfold HeapOK' in H10. specialize (H10 (length h) c TSUnique obj).
    rewrite indexr_head in H10. intuition. destruct H8 as [fl [init [ml H8]]].
    intuition. exists &(length h). rewrite H2. rewrite indexr_head. intuition. 
    eapply runtime_ty_unique; eauto. apply indexr_var_some' in H10; auto.
    rewrite indexr_head; eauto. left. exists (length σ). unfold unique. intuition.
    rewrite indexr_head; auto. 1:{ destruct (x' =? length σ) eqn: E2.
    - apply Nat.eqb_eq in E2; subst; auto.
    - apply Nat.eqb_neq in E2. rewrite indexr_skip in H11; auto.
      apply indexr_var_some' in H11 as Heq. rewrite <- H2 in Heq.
      apply indexr_var_some in Heq. destruct Heq as [Tx Heq]. specialize (H6 x' Tx).
      intuition. destruct H6 as [c' [v' H6]]. intuition. subst. rewrite H11 in H14;
      inversion H14. destruct H6 as [vx H6]. intuition. rewrite H13 in H11; inversion H11; subst.
      specialize (H17 c TSUnique). intuition. destruct H16 as [l' [fvalues H16]].
      intuition. inversion H16. subst. lia. }
    rewrite <- H2. econstructor; eauto. rewrite indexr_head; auto. discriminate.
    inversion H11; subst. exists (length h), obj. intuition. rewrite indexr_head; auto.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H5; auto. specialize (H6 x Tx).
    rewrite H2 in E1. rewrite indexr_skip; auto. intuition. right. destruct H6 as [vx H6].
    exists vx. intuition. inversion H8; subst. 1-3: econstructor; eauto. 
    1,2: apply indexr_var_some' in H12 as Hl. rewrite indexr_skip; eauto. lia.
    eapply runtime_ty_unique; eauto. rewrite indexr_skip; eauto. lia. { intuition.
    + left. inversion H14. exists x0. unfold unique in *. intuition. apply indexr_var_some' in H15 as H';
      auto. rewrite indexr_skip; auto. lia. destruct (x' =? length σ) eqn: E3.
      - apply Nat.eqb_eq in E3; subst. rewrite indexr_head in H13. inversion H13; subst. lia.
      - apply Nat.eqb_neq in E3. rewrite indexr_skip in H13. specialize (H16 x'). intuition. lia.
    + right. intros. destruct H13. destruct (x0 =? length σ) eqn: E3.
      - apply Nat.eqb_eq in E3; subst. rewrite indexr_head in H13; inversion H13; subst. lia.
      - apply Nat.eqb_neq in E3. rewrite indexr_skip in H13. 
        assert (exists x : nat, indexr x σ = Some (TCls c0 TSUnique, & l)). exists x0. auto.
        apply H14 in H15; auto. lia. }
    inversion H9; subst; econstructor; eauto. rewrite <- H2 in E1. 1,2: rewrite indexr_skip; auto. lia.
    inversion H10; subst. specialize (H11 c0 ts). intuition. destruct H10 as [l [fvalues H10]].
    exists l, fvalues. intuition. simpl. lia. apply indexr_var_some' in H14 as Hl.
    rewrite indexr_skip; auto. lia.
Qed.

Lemma HeapOK_ext_unique_pure: forall {Γ σ h ct c obj}, CtxOK Γ σ h ct ->
  CtxOK Γ σ ((TCls c TSUnique, obj) :: h) ct ->
  HeapOK ((TCls c TSUnique) :: Γ) ((TCls c TSUnique, &(length h)) :: σ) ((TCls c TSUnique, obj) :: h) ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK in *. intuition. destruct (x =? length Γ) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. inversion H1. rewrite H5. rewrite indexr_head; auto.
    inversion H0; intuition. unfold HeapOK' in H11. specialize (H11 (length h) c TSUnique obj).
    rewrite indexr_head in H11. intuition. destruct H8 as [fl [init [ml H8]]].
    intuition. exists fl, init, ml, (length h). inversion H2; subst. rewrite indexr_head in H18.
    inversion H18; subst. intuition. specialize (H13 f). apply indexr_var_some' in H12 as Hf.
    rewrite H8 in Hf. intuition. destruct H14 as [T' [v' H14]]. exists v', obj. intuition.
    rewrite indexr_head; auto. rewrite H17 in H12; inversion H12; subst. auto.
    econstructor; eauto. specialize (StoreOK_wf_ct H1) as Hwf. specialize (wf_ct_to_Tf Hwf H11 H12);
    auto. apply indexr_var_some' in H11; auto. econstructor; eauto. rewrite <- H5. 
    rewrite indexr_head; auto. econstructor; eauto. specialize (StoreOK_wf_ct H1) as Hwf.
    specialize (wf_ct_to_Tf Hwf H11 H12); auto. inversion H15; subst; rewrite H12 in H17;
    inversion H17; subst. 1-3: econstructor; eauto. eapply runtime_ty_unique; eauto.
    specialize (StoreOK_wf_ct H1) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H11 H12) as Heq.
    contradiction.
  + apply Nat.eqb_neq in E1. inversion H1. assert (tm_has_ty Γ ct $ x (TCls c0 ts)).
    inversion H2; subst. econstructor; eauto. rewrite indexr_skip in H12; auto.
    specialize (H3 x c0 ts). intuition. destruct H6 as [fl [init [ml [oid H6]]]].
    exists fl, init, ml, oid. intuition. rewrite H5 in E1. rewrite indexr_skip; auto.
    specialize (H11 f Tf). intuition. destruct H12 as [vf [object H12]]. exists vf, object.
    intuition. apply indexr_var_some' in H11 as Hoid. rewrite indexr_skip; auto. lia.
    inversion H14; subst. econstructor; eauto. inversion H20; subst. econstructor; eauto.
    rewrite indexr_skip; auto. inversion H16; subst. 1-3: econstructor; eauto.
    apply indexr_var_some' in H17 as Hl. rewrite indexr_skip; eauto. lia.
    specialize (StoreOK_wf_ct H1) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H6 H10) as Heq.
    contradiction. 
Qed.

Lemma HeapOK'_ext_unique_pure: forall {Γ σ h ct c obj}, CtxOK Γ σ h ct ->
  CtxOK Γ σ ((TCls c TSUnique, obj) :: h) ct ->
  HeapOK' ((TCls c TSUnique) :: Γ) ((TCls c TSUnique, &(length h)) :: σ) ((TCls c TSUnique, obj) :: h) ct.
Proof.
  intros. inversion H0; intuition. unfold HeapOK' in *. intuition. specialize (H4 o c0 ts object).
  intuition. destruct H5 as [fl [init [ml H5]]]. exists fl, init, ml. intuition. specialize (H7 f).
  intuition. destruct H8 as [T' [v' H8]]. exists T', v'. intuition. inversion H9; subst.
  1-3: econstructor; eauto. specialize (StoreOK_wf_ct H1) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H4 H11) as Heq.
  contradiction.
Qed.

Lemma CtxOK_ext_unique_pure: forall {Γ σ h ct c obj}, CtxOK Γ σ h ct ->
  CtxOK Γ σ ((TCls c TSUnique, obj) :: h) ct ->
  CtxOK ((TCls c TSUnique) :: Γ) ((TCls c TSUnique, &(length h)) :: σ) ((TCls c TSUnique, obj) :: h) ct.
Proof.
  intros. unfold CtxOK; intuition. eapply StoreOK_ext_unique_pure; eauto.
  eapply HeapOK_ext_unique_pure; eauto. eapply HeapOK'_ext_unique_pure; eauto.
Qed.

Lemma StoreOK_heap_ext: forall {Γ σ h ct c d objrec fs init ms ts}, CtxOK Γ σ h ct -> 
  indexr c ct = Some (cls_def d fs init ms) ->
  object_valid_semantic objrec σ h ct fs ->
  StoreOK Γ σ ((TCls c ts, objrec) :: h) ct.
Proof.
  intros. inversion H. unfold StoreOK in *. intuition. specialize (H7 x Tx). intuition. right.
  destruct H7 as [vx H8]. exists vx. intuition. eapply weakening_tm_runtime; eauto.
  specialize (H12 c0 ts0); intuition. destruct H13 as [l [fvalues H13]]. exists l, fvalues.
  intuition. assert(length ((TCls c ts, objrec) :: h) = S (length h)) by auto.
  rewrite H12; lia. apply indexr_var_some' in H15 as H16. rewrite indexr_skip; eauto; lia.
Qed.

Lemma HeapOK_heap_ext: forall {Γ σ h ct c d objrec fs init ms ts}, CtxOK Γ σ h ct -> 
  indexr c ct = Some (cls_def d fs init ms) ->
  object_valid_semantic objrec σ h ct fs ->
  HeapOK Γ σ ((TCls c ts, objrec) :: h) ct.
Proof.
  intros. inversion H. unfold HeapOK in *. intuition. specialize (H4 x c0 ts0).
  intuition. destruct H6 as [fl' [init' [ml' [oid' H6]]]]. exists fl', init', ml', oid'.
  intuition. specialize (H8 f Tf). intuition. destruct H9 as [vf [object H9]].
  exists vf, object. intuition. apply indexr_var_some' in H8 as H15. rewrite indexr_skip; eauto; lia.
  all: eapply weakening_tm_runtime; eauto.
Qed.

Lemma HeapOK'_heap_ext: forall {Γ σ h ct c d objrec fs init ms ts}, CtxOK Γ σ h ct -> 
  indexr c ct = Some (cls_def d fs init ms) ->
  object_valid_semantic objrec σ h ct fs ->
  HeapOK' Γ σ ((TCls c ts, objrec) :: h) ct.
Proof.
  intros. inversion H. unfold HeapOK' in *. intuition. destruct (o =? (length h)) eqn: E1.
  + apply Nat.eqb_eq in E1. specialize (H5 o c0 ts0 object). subst. rewrite indexr_head in *.
    inversion H3; subst. intuition. exists fs, init, ms. intuition. inversion H1; subst.
    auto. assert (length (T :: fs0) = S (length fs0)) by auto.
    assert (length ((T, v) :: o) = S (length o)) by auto. lia. apply indexr_var_some in H6.
    destruct H6 as [(T, v) H6]. exists T, v. specialize (object_valid_hit H1 H6) as H7.
    intuition. eapply weakening_tm_runtime; eauto.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H3; auto. specialize (H5 o c0 ts0 object).
    intuition. destruct H6 as [fl' [init' [ml' H6]]]. exists fl', init', ml'. intuition.
    specialize (H8 f). intuition. destruct H9 as [T [v H9]]. exists T, v. intuition.   
    eapply weakening_tm_runtime; eauto.
Qed.

Lemma CtxOK_heap_ext: forall {Γ σ h ct c d objrec fs init ms ts}, CtxOK Γ σ h ct -> 
  indexr c ct = Some (cls_def d fs init ms) ->
  object_valid_semantic objrec σ h ct fs ->
  CtxOK Γ σ ((TCls c ts, objrec) :: h) ct.
Proof.
  intros. unfold CtxOK; intuition. 
  eapply StoreOK_heap_ext; eauto.
  eapply HeapOK_heap_ext; eauto.
  eapply HeapOK'_heap_ext; eauto.
Qed. 

Lemma CtxOK_trim_StoreOK: forall {Γ σ h ct T v}, CtxOK (T::Γ) ((T, v)::σ) h ct ->
  StoreOK Γ σ h ct.
Proof.
  intros. inversion H. unfold StoreOK in *. intuition. specialize (H5 x Tx).
  assert (indexr x (T :: Γ) = Some Tx). all: apply indexr_var_some' in H3 as H3'.
  rewrite indexr_skip; auto; lia. assert (length Γ = length σ). simpl in H2. lia.
  intuition.
  + left. destruct H5 as [c [vx H5]]. exists c, vx. intuition. rewrite indexr_skip in H9;
    auto. rewrite <- H7. lia.
  + right. destruct H5 as [vx H5]. exists vx. intuition. rewrite H7 in H3'.
    rewrite indexr_skip in H8; auto; lia. 2: { inversion H10; subst. rewrite indexr_skip in H15;
    try lia. econstructor; eauto. rewrite indexr_skip in H13; try lia. econstructor; eauto. }
    inversion H9; subst. 1-3: econstructor; eauto. eapply runtime_ty_unique; eauto.
    intuition.
    - destruct H15. destruct (x0 =? length σ) eqn: E1.
      * right. apply Nat.eqb_eq in E1; subst. intros. unfold unique in H14.
        intuition. destruct H15. apply indexr_var_some' in H14 as H14'.
        specialize (H17 x0). assert (indexr x0 ((T, v) :: σ) = Some (TCls c TSUnique, & l)).
        erewrite indexr_skip; eauto; lia. intuition.
      * left. apply Nat.eqb_neq in E1. exists x0. unfold unique in *. intuition.
        rewrite indexr_skip in H15; auto; try lia. specialize (H16 x').
        rewrite indexr_skip in H16; auto. apply indexr_var_some' in H14; lia.
    - right. intros. destruct H14. assert (exists x : nat, indexr x ((T, v) :: σ) = Some (TCls c TSUnique, & l)).
      exists x0. apply indexr_var_some' in H14 as H14'; try lia. rewrite indexr_skip; auto. lia.
      apply H15 in H16; auto.
Qed.

Lemma CtxOK_trim_HeapOK: forall {Γ σ h ct T v}, CtxOK (T::Γ) ((T, v)::σ) h ct ->
  HeapOK Γ σ h ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK in *. intuition. specialize (H2 x c ts).
  inversion H1; subst. assert (tm_has_ty (T :: Γ) ct $ x (TCls c ts)).
  eapply weakening_tm; auto. intuition. destruct H5 as [fl [init [ml [l H5]]]].
  exists fl, init, ml, l. intuition. apply indexr_var_some' in H9 as H9'. inversion H0.
  assert (length Γ = length σ). simpl in H6. lia. rewrite H12 in H9'. 
  rewrite indexr_skip in H2; auto; try lia. specialize (H7 f Tf). intuition.
  destruct H8 as [vf [object H8]]. exists vf, object. intuition. inversion H13; subst.
  econstructor; eauto. inversion H19; subst. apply indexr_var_some' in H9. 
  inversion H0. assert (length Γ = length σ). simpl in H14. lia. rewrite H20 in H9.
  rewrite indexr_skip in H25; try lia. econstructor; eauto.
  inversion H15; subst. 1-3: econstructor; eauto. specialize (StoreOK_wf_ct H0) as Hwf.
  specialize (wf_ct_to_Tf_ts Hwf H5 H6) as Heq. contradiction.
Qed.

Lemma CtxOK_trim_HeapOK': forall {Γ σ h ct T v}, CtxOK (T::Γ) ((T, v)::σ) h ct ->
  HeapOK' Γ σ h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK' in *. intuition. specialize (H3 o c ts object).
  intuition. destruct H4 as [fl [init [ml H4]]]. exists fl, init, ml. intuition.
  specialize (H6 f). intuition. destruct H7 as [T0 [v0 H7]]. exists T0, v0. intuition.
  inversion H8; subst. 1-3: econstructor; eauto. specialize (StoreOK_wf_ct H0) as Hwf.
  specialize (wf_ct_to_Tf_ts Hwf H3 H10) as Heq. contradiction.
Qed.

Lemma CtxOK_trim: forall {Γ σ h ct T v}, CtxOK (T::Γ) ((T, v)::σ) h ct ->
  CtxOK Γ σ h ct.
Proof.
  intros. unfold CtxOK. intuition. eapply CtxOK_trim_StoreOK; eauto.
  eapply CtxOK_trim_HeapOK; eauto. eapply CtxOK_trim_HeapOK'; eauto.
Qed.
 
(* Lemma update_store_heapOK: forall {Γ σ h ct x T v}, CtxOK Γ σ h ct ->
      indexr x Γ = Some T ->
      value_runtime_ty σ h ct v T -> value v ->
      HeapOK Γ (update σ x (T, v)) h ct.
Proof.
  (* introduce hypothesis *)
  intros. inversion H. intuition. unfold HeapOK in *. intuition.
  inversion H4; subst. destruct (Nat.eqb x x0) eqn: Heq; auto.
  (* devide into x = x0 and x != x0 *)
  + apply Nat.eqb_eq in Heq. subst. rewrite H0 in H12. inversion H12; subst.
    induction H2; inversion H1; subst. specialize (H5 x0 c ts). intuition.
    destruct H2 as [fl [init [ml [oid H2]]]]. intuition. exists fl, init, ml, o.
    intuition. apply indexr_var_some' in H5 as H5'. apply update_indexr_hit. auto.
    specialize (H8 f Tf). intuition. destruct H9 as [vf [obj H9]]. 
    unfold HeapOK' in H6. specialize(H6 o c ts fs). intuition. 
    destruct H15 as [fl' [init' [ml' H15]]]. intuition. rewrite H6 in H2. 
    inversion H2; subst. specialize (H18 f). specialize (indexr_var_some' H7) as H19.
    rewrite H15 in H19. intuition. destruct H17 as [T' [v' H17]]. intuition.
    rewrite H22 in H7; inversion H7; subst. exists v', fs. intuition.
    admit. admit.
    (* should I add wf_class to the definition of oid type judgement? *)
  + apply Nat.eqb_neq in Heq. specialize (H5 x0 c). intuition.
    eapply update_indexr_miss in Heq. rewrite Heq. intuition. admit.
Admitted. *)

Lemma update_store_TBool_StoreOK: forall {Γ σ h ct x v}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x TBool ->
  value_runtime_ty σ h ct v TBool  -> value v ->
  StoreOK Γ (update σ x (TBool, v)) h ct.
Proof.
  intros. inversion H. unfold StoreOK in *. intuition. rewrite <- update_length; auto. 
  specialize (H8 x0 Tx). intuition.
  + left. destruct H8 as [c [vx H8]]. exists c, vx. intuition. inversion H9; subst.
    destruct (x0 =? x) eqn: E1. apply Nat.eqb_eq in E1; subst; rewrite update_indexr_hit; auto.
    inversion H0; subst. rewrite H13 in H6; inversion H6. apply indexr_var_some' in H6; auto.
    rewrite <- H5; auto. apply Nat.eqb_neq in E1. rewrite update_indexr_miss; auto.
  +  right. destruct (Nat.eqb x x0) eqn: Heq; auto.
    - apply Nat.eqb_eq in Heq. subst. inversion H0; subst. rewrite H12 in H6; inversion H6; subst.
      exists v. intuition. eapply update_indexr_hit; eauto. apply indexr_var_some' in H12; rewrite <- H5; auto. 
      induction H2. 1,2: econstructor; eauto. inversion H1. inversion H9. 
    - apply Nat.eqb_neq in Heq. destruct H8 as [v0 H16']. intuition. exists v0. intuition. 
      erewrite update_indexr_miss; eauto. inversion H. inversion H12; intuition.
      specialize (H19 x TBool). inversion H0; subst. intuition. destruct H19 as [c' [v' H19]].
      intuition. inversion H16. destruct H19 as [vx H19]. intuition.
      inversion H9; subst. 1,2,3: econstructor; eauto. eapply runtime_ty_unique; eauto. destruct H26. 
      * left. destruct H26. exists x1. unfold unique in *. 
        destruct (x1 =? x) eqn: E2. intuition.
          1,2: apply Nat.eqb_eq in E2; subst; rewrite H27 in H16; inversion H16.
          apply Nat.eqb_neq in E2. erewrite update_indexr_miss; eauto. intuition.
          destruct (x' =? x) eqn: E3. 
            apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H26; eauto. inversion H26.
            specialize (indexr_var_some' H16) as H30; auto.
            apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H26; eauto.
      * right. unfold not in *. intros. destruct H27. destruct (x1 =? x) eqn:E1.
        ++  apply Nat.eqb_eq in E1; subst. erewrite update_indexr_hit in H27; eauto.
            apply indexr_var_some' in H16; auto.
        ++  apply Nat.eqb_neq in E1. erewrite update_indexr_miss in H27; eauto.
Qed.

Lemma update_store_TBool_heapOK: forall {Γ σ h ct x v}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x TBool ->
  value_runtime_ty σ h ct v TBool  -> value v ->
  HeapOK Γ (update σ x (TBool, v)) h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK in *. intuition. specialize (H5 x0 c ts).
  intuition. destruct H7 as [fl [init [ml [oid H7]]]]. intuition. destruct (x0 =? x) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. inversion H0; inversion H4; subst. rewrite H12 in H18; inversion H18.
  + apply Nat.eqb_neq in E1. exists fl, init, ml, oid. erewrite update_indexr_miss; eauto.
    intuition. specialize (H9 f Tf). intuition. destruct H10 as [vf [object H10]].
    intuition. exists vf, object. intuition. induction H14. 1,2: econstructor.
    econstructor; eauto. eapply runtime_ty_unique; eauto. destruct H15.
    ++  left. destruct H15. inversion H3. intuition. specialize (H19 x TBool). 
        inversion H0; subst. intuition. destruct H19 as [c' [v' H19]]. intuition. inversion H17.
        destruct H19 as [vx H19]. destruct (x1 =? x) eqn: E2.
          - apply Nat.eqb_eq in E2; subst. unfold unique in H15. intuition.
            rewrite H17 in H15; inversion H15.
          - apply Nat.eqb_neq in E2. exists x1. unfold unique in *. erewrite update_indexr_miss; eauto.
            intuition. destruct (x' =? x) eqn: E3.
              * apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H24. inversion H24.
                eapply indexr_var_some'; eauto.
              * apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H24; auto.
    ++  right. unfold not in *. intros. destruct H16. destruct (x1 =? x) eqn:E2.
        - apply Nat.eqb_eq in E2; subst. erewrite update_indexr_hit in H16; eauto.
          inversion H16. inversion H0; subst. eapply indexr_var_some' in H20. inversion H3.
          rewrite <- H17; auto.
        - apply Nat.eqb_neq in E2. erewrite update_indexr_miss in H16; eauto. 
Qed. 

Lemma update_store_TBool_heapOK': forall {Γ σ h ct x v}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x TBool ->
  value_runtime_ty σ h ct v TBool  -> value v ->
  HeapOK' Γ (update σ x (TBool, v)) h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK' in *. intuition. specialize (H6 o c ts object).
  intuition. destruct H7 as [fl [init [ml H7]]]. exists fl, init, ml. intuition. 
  specialize (H9 f). intuition. destruct H10 as [T' [v' H10]]. exists T' ,v'.
  intuition. induction H11. 1,2,3: econstructor; eauto. eapply runtime_ty_unique; eauto. 
  destruct H14. 
  * left. destruct H14. inversion H3. intuition. specialize (H18 x TBool). inversion H0; subst. 
    intuition. destruct H18 as [c' [v' H18]]. intuition. inversion H16. destruct H18 as [vx H19].
    destruct (x0 =? x) eqn: E1.
    + apply Nat.eqb_eq in E1; subst. unfold unique in H14. intuition. rewrite H16 in H14; inversion H14.
    + apply Nat.eqb_neq in E1. exists x0. unfold unique in *. erewrite update_indexr_miss; eauto. intuition.
      destruct (x' =? x) eqn: E2. 
      - apply Nat.eqb_eq in E2; subst. rewrite update_indexr_hit in H23; eauto. inversion H23.
        eapply indexr_var_some'; eauto.
      - apply Nat.eqb_neq in E2. rewrite update_indexr_miss in H23; auto.
  * right. unfold not in *. intros. destruct H15. destruct (x0 =? x) eqn:E1.
    + apply Nat.eqb_eq in E1; subst. erewrite update_indexr_hit in H15; eauto.
      inversion H15. inversion H0; subst. eapply indexr_var_some' in H19. 
      inversion H3. rewrite H16 in H19; auto.
    + apply Nat.eqb_neq in E1. erewrite update_indexr_miss in H15; eauto.
Qed.

Lemma update_store_TBool_CtxOK: forall {Γ σ h ct x v}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x TBool ->
  value_runtime_ty σ h ct v TBool  -> value v ->
  CtxOK Γ (update σ x (TBool, v)) h ct.
Proof.
  intros. unfold CtxOK. intuition. eapply update_store_TBool_StoreOK; eauto.
  eapply update_store_TBool_heapOK; eauto. eapply update_store_TBool_heapOK'; eauto.
Qed.

Lemma update_store_shared_storeOK: forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSShared) ->
  indexr y σ = Some (TCls c TSShared, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSShared) ->
  StoreOK (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, & l)) h ct.
Proof.
  intros. inversion H. unfold StoreOK in *. repeat erewrite <- update_length. intuition.
  destruct (x0 =? x) eqn: E1.
  + apply Nat.eqb_eq in E1; inversion H0; subst. specialize (H9 x (TCls c ts)).
    intuition. right. exists (&l). rewrite update_indexr_hit in H7; auto.
    inversion H7; subst. rewrite update_indexr_hit; auto. 
    2,3: apply indexr_var_some' in H15; auto; try rewrite <- H6; auto. intuition.
    inversion H3; econstructor; eauto. inversion H1; econstructor; eauto.
    rewrite update_indexr_hit; auto. apply indexr_var_some' in H15; auto.
    inversion H3; subst. inversion H10; subst. exists l, fs. intuition.
    apply indexr_var_some' in H21; auto. right.
    destruct H9 as [vx H10]. exists (& l). intuition. 
    1,2,3,4: rewrite update_indexr_hit in H7; auto;
    inversion H7; subst. rewrite update_indexr_hit; auto. 
    1,2,4,6,8: apply indexr_var_some' in H15; auto; try rewrite <- H6; auto. 
    inversion H3; econstructor; eauto. econstructor; eauto.
    rewrite update_indexr_hit; auto. apply indexr_var_some' in H15; auto.
    discriminate. inversion H1; subst. auto.
    inversion H3; subst. inversion H7; subst. exists l, fs. intuition.
    apply indexr_var_some' in H25; auto. 
  + apply Nat.eqb_neq in E1. inversion H0; subst. specialize (H9 x0 Tx).
    erewrite update_indexr_miss in H7; eauto. intuition.
    - left. rewrite update_indexr_miss; auto.
    - right. destruct H9 as [vx H9]. exists vx. intuition.
      rewrite update_indexr_miss; auto. inversion H11; subst.
      1-3: econstructor; eauto. eapply runtime_ty_unique; eauto. 1: { intuition.
      * destruct H20. destruct (x1 =? x) eqn:E2.
        -- apply Nat.eqb_eq in E2; subst. right. intros. destruct H20.
          destruct (x1 =? x) eqn: E3. 
          ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H20; eauto. 
            inversion H20. eapply indexr_var_some' in H15. rewrite H6 in H15; eauto.
          ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H20; eauto.
            unfold unique in H19. intuition. specialize (H22 x1). intuition.
        -- apply Nat.eqb_neq in E2. left. exists x1. unfold unique in *.
          intuition. erewrite update_indexr_miss; eauto. erewrite update_indexr_miss in H19; eauto.
          destruct (x' =? x) eqn: E3.
          ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H19; eauto. inversion H19.
            eapply indexr_var_some' in H15. rewrite H6 in H15; eauto.
          ++ apply Nat.eqb_neq in E3. auto.
      * right. unfold not in *. intros. destruct H19. destruct (x1 =? x) eqn: E2.
        -- apply Nat.eqb_eq in E2; subst. erewrite update_indexr_hit in H19; eauto.
          eapply indexr_var_some' in H15. rewrite H6 in H15; eauto.
        -- apply Nat.eqb_neq in E2. erewrite update_indexr_miss in H19; eauto. }
      inversion H12; subst; econstructor; eauto. all: rewrite update_indexr_miss; auto.
Qed.

Lemma update_store_shared_heapOK: forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSShared) ->
  indexr y σ = Some (TCls c TSShared, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSShared) ->
  HeapOK (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, & l)) h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK in *. intuition. destruct (x0 =? x) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. inversion H5; subst. specialize (indexr_var_some' H13) as H13'.
    erewrite <- update_length in H13'. erewrite update_indexr_hit in H13; eauto.
    inversion H13; subst. inversion H0; subst. specialize (H6 x c0 ts). intuition.
    destruct H8 as [fl [init [ml [oid H8]]]]. exists fl, init, ml, l. intuition.
    erewrite update_indexr_hit; eauto. eapply indexr_var_some'; eauto.
    inversion H3; subst. unfold HeapOK' in H7. specialize (H7 l c0 TSShared fs).
    intuition. destruct H11 as [fl' [init' [ml' H11]]]. intuition.
    rewrite H7 in H8; inversion H8; subst. specialize (H19 f). 
    specialize (indexr_var_some' H9) as H10'. rewrite H11 in H10'. intuition.
    destruct H12 as [T' [vf H12]]. exists vf, fs. intuition. 1,2: rewrite H22 in H9; subst;
    inversion H9; subst; auto. specialize (H10 f Tf). intuition. destruct H21 as [vf' [object' H21]].
    intuition. inversion H27; subst. inversion H33; subst. rewrite H39 in H16; inversion H16; subst.
    econstructor; eauto. rewrite H22 in H9; inversion H9; subst. inversion H20; subst.
    1-3: econstructor; eauto. eapply runtime_ty_unique; eauto. intuition.
    - destruct H28. destruct (x0 =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. right. intros. destruct H28. destruct (x0 =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H28; eauto. inversion H28.
           specialize (indexr_var_some' H6) as H6'; auto.
        ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H28; eauto.
           unfold unique in H27. intuition. specialize (H30 x0). intuition.
      * apply Nat.eqb_neq in E2. left. exists x0. unfold unique in *. intuition.
        erewrite update_indexr_miss; eauto. destruct (x' =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H27; eauto.
           inversion H27. specialize (indexr_var_some' H6) as H6'; auto.
        ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H27; eauto.
    - right. intros. destruct H27. destruct (x0 =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. erewrite update_indexr_hit in H27; eauto.
        inversion H27. specialize (indexr_var_some' H6) as H6'; auto.
      * apply Nat.eqb_neq in E2. erewrite update_indexr_miss in H27; eauto.
  + apply Nat.eqb_neq in E1. inversion H5; subst. specialize (indexr_var_some' H13) as H13'.
    erewrite <- update_length in H13'. erewrite update_indexr_miss in H13; eauto.
    assert (tm_has_ty Γ ct $ x0 (TCls c0 ts0)). econstructor; eauto.
    specialize (H6 x0 c0 ts0). intuition. destruct H9 as [fl [init [ml [oid H9]]]].
    exists fl, init, ml, oid. intuition. erewrite update_indexr_miss; eauto.
    specialize (H11 f Tf). intuition. destruct H12 as [vf [object H12]].
    exists vf, object. intuition. inversion H17; subst. econstructor; eauto.
    inversion H23; subst. econstructor; eauto. erewrite update_indexr_miss; eauto.
    inversion H19; subst. 1-3: econstructor; eauto.
    eapply runtime_ty_unique; eauto. intuition.
    - destruct H22. destruct (x1 =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. right. intros. destruct H22.
        destruct (x1 =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H22; eauto.
           inversion H22. inversion H0; subst. specialize (indexr_var_some' H28) as H20'.
           inversion H4. rewrite H23 in H20'; auto.
        ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H22; eauto.
           unfold unique in H21; intuition. specialize (H24 x1). intuition.
      * apply Nat.eqb_neq in E2. left. exists x1. unfold unique in *.
        intuition. erewrite update_indexr_miss; eauto. erewrite update_indexr_miss in H21; eauto.
        destruct (x' =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H21; eauto.
           inversion H21. inversion H0; subst. specialize (indexr_var_some' H29) as H20'.
           inversion H4. rewrite H24 in H20'; auto.
        ++ apply Nat.eqb_neq in E3. auto.
    - right. intros. destruct H21. destruct (x1 =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. erewrite update_indexr_hit in H21; eauto.
        inversion H21. inversion H0; subst. specialize (indexr_var_some' H28) as H20'.
        inversion H4. rewrite H23 in H20'; auto.
      * apply Nat.eqb_neq in E2. erewrite update_indexr_miss in H21; eauto.
Qed.

Lemma update_store_shared_heapOK': forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSShared) ->
  indexr y σ = Some (TCls c TSShared, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSShared) ->
  HeapOK' (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, & l)) h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK' in *. intuition.
  specialize (H7 o c0 ts0 object). intuition. destruct H8 as [fl [init [ml H8]]].
  exists fl, init, ml. intuition. specialize (H10 f). intuition.
  destruct H11 as [T' [v' H11]]. exists T', v'. intuition.
  inversion H12; subst. 1-3: econstructor; eauto. 
  eapply runtime_ty_unique; eauto. intuition.
  + destruct H17. destruct (x0 =? x) eqn: E1.
    - apply Nat.eqb_eq in E1; subst. right. intros. destruct H17.
      destruct (x0 =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. erewrite update_indexr_hit in H17; eauto.
        inversion H17. inversion H0; subst. apply indexr_var_some' in H23.
        inversion H4. rewrite H18 in H23; auto.
      * apply Nat.eqb_neq in E2. erewrite update_indexr_miss in H17; eauto.
        unfold unique in H16. intuition. specialize (H19 x0). intuition.
    - apply Nat.eqb_neq in E1. left. exists x0. unfold unique in *.
      intuition. erewrite update_indexr_miss; eauto.
      erewrite update_indexr_miss in H16; eauto.
      destruct (x' =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. erewrite update_indexr_hit in H16; eauto.
        inversion H16. inversion H0; subst. apply indexr_var_some' in H24.
        inversion H4. rewrite H19 in H24; auto.
      *  apply Nat.eqb_neq in E2. auto.
  + right. intros. destruct H16. destruct (x0 =? x) eqn:E1.
    - apply Nat.eqb_eq in E1; subst. erewrite update_indexr_hit in H16; eauto.
    inversion H16. inversion H0; subst. apply indexr_var_some' in H23.
    inversion H4. rewrite H18 in H23; auto.
    - apply Nat.eqb_neq in E1. erewrite update_indexr_miss in H16; eauto.
Qed.

Lemma update_store_shared_CtxOK: forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSShared) ->
  indexr y σ = Some (TCls c TSShared, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSShared) ->
  CtxOK (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, & l)) h ct.
Proof.
  intros. unfold CtxOK. intuition. eapply update_store_shared_storeOK; eauto.
  eapply update_store_shared_heapOK; eauto. eapply update_store_shared_heapOK'; eauto.
Qed.

Lemma update_store_unique_storeOK: forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSUnique) ->
  indexr y σ = Some (TCls c TSUnique, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSUnique) ->
  StoreOK (update (update Γ y (TCls c TSBot)) x (TCls c TSUnique))
  (update (update σ y (TCls c TSBot, & l)) x (TCls c TSUnique, & l)) h ct.
Proof.
  intros. inversion H. unfold StoreOK in *. repeat rewrite <- update_length. intuition.
  destruct (x0 =? x) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. inversion H0; subst. specialize (H9 x (TCls c ts)) as H9'.
    intuition. 
    ** right. exists (&l). erewrite update_indexr_hit in H7; eauto. 
      inversion H7; subst. 2: eapply indexr_var_some' in H15; erewrite <- update_length; eauto.
      specialize (indexr_var_some' H15) as Heq1. erewrite update_indexr_hit; eauto. 
      2:{ rewrite <- update_length. rewrite <- H6. auto. } intuition.
      inversion H3; subst. contradiction. eapply runtime_ty_unique; eauto. 1: { intuition.
      - left. destruct H10. unfold unique in H10. intuition. specialize (H14 y) as H15'.
        intuition; subst. exists x. unfold unique. intuition.
        erewrite update_indexr_hit; eauto. rewrite <- update_length. rewrite <- H6; auto.
        destruct (x' =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst; auto.
        ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H10; eauto.
            destruct (x' =? y) eqn: E4.
            -- apply Nat.eqb_eq in E4; subst. erewrite update_indexr_hit in H10; eauto.
                inversion H10. eapply indexr_var_some'; eauto.
            -- apply Nat.eqb_neq in E4. erewrite update_indexr_miss in H10; eauto.
                specialize (H14 x'); intuition.
      - destruct H10. exists y. auto. }
      - inversion H1; subst. econstructor; eauto. rewrite update_indexr_hit; auto.
        apply indexr_var_some' in H15; rewrite <- update_length; auto.
      - inversion H1; subst. specialize (H9 y (TCls c TSUnique)). intuition. 
        destruct H9 as [c' [v' H9]]. intuition. inversion H12.
        destruct H9 as [vx H9]. intuition. specialize (H19 c TSUnique). intuition.
        destruct H18 as [l' [fs' H18]]. intuition. rewrite H12 in H2; inversion H2; subst.
        inversion H25; subst. inversion H10; subst. exists l, fs'. intuition.
    ** right. exists (&l). erewrite update_indexr_hit in H7; eauto. 
      inversion H7; subst. 2: eapply indexr_var_some' in H15; erewrite <- update_length; eauto.
      specialize (indexr_var_some' H15) as Heq1. erewrite update_indexr_hit; eauto. 
      2:{ rewrite <- update_length. rewrite <- H6. auto. } intuition.
      inversion H3; subst. contradiction. eapply runtime_ty_unique; eauto. 1: { intuition.
      - left. destruct H10. unfold unique in H10. intuition. specialize (H14 y) as H15'.
        intuition; subst. exists x. unfold unique. intuition.
        erewrite update_indexr_hit; eauto. rewrite <- update_length. rewrite <- H6; auto.
        destruct (x' =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst; auto.
        ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H10; eauto.
            destruct (x' =? y) eqn: E4.
            -- apply Nat.eqb_eq in E4; subst. erewrite update_indexr_hit in H10; eauto.
                inversion H10. eapply indexr_var_some'; eauto.
            -- apply Nat.eqb_neq in E4. erewrite update_indexr_miss in H10; eauto.
                specialize (H14 x'); intuition.
      - destruct H10. exists y. auto. }
      - inversion H1; subst. econstructor; eauto. rewrite update_indexr_hit; auto.
        apply indexr_var_some' in H15; rewrite <- update_length; auto.
      - inversion H1; subst. specialize (H9 y (TCls c TSUnique)). intuition. 
        destruct H9 as [c' [v' H9]]. intuition. inversion H12.
        destruct H9 as [vx H9]. intuition. specialize (H19 c TSUnique). intuition.
        destruct H18 as [l' [fs' H18]]. intuition. rewrite H12 in H2; inversion H2; subst.
        inversion H25; subst. inversion H10; subst. exists l, fs'. intuition.
  + apply Nat.eqb_neq in E1. destruct (x0 =? y) eqn: E2.
    - apply Nat.eqb_eq in E2; subst. erewrite update_indexr_miss in H7; eauto; 
      erewrite update_indexr_hit in H7; eauto.
      2: { rewrite H6. eapply indexr_var_some'; eauto. } inversion H7; subst.
      left. exists c, &l. intuition. erewrite update_indexr_miss; eauto. 
      erewrite update_indexr_hit; eauto. eapply indexr_var_some' in H2; eauto.
    - apply Nat.eqb_neq in E2. erewrite update_indexr_miss in H7; eauto.
      erewrite update_indexr_miss in H7; eauto. specialize (H9 x0 Tx).
      intuition. left. destruct H9 as [c' [v' H9]]. exists c', v'. intuition.
      rewrite update_indexr_miss; auto; rewrite update_indexr_miss; auto.
      right. destruct H9 as [vx H9]. exists vx. intuition. rewrite update_indexr_miss; auto.
      rewrite update_indexr_miss; auto. 2:{ inversion H12; subst; econstructor; eauto. all:
      rewrite update_indexr_miss; auto; rewrite update_indexr_miss; auto. }
      inversion H11; subst. 1-3: econstructor; eauto. eapply runtime_ty_unique; eauto. intuition.
      * left. destruct H17. unfold unique in *. intuition. specialize (H18 x0) as H20'.
        intuition. subst. exists x0. repeat erewrite update_indexr_miss; eauto.
        intuition. destruct (x' =? x) eqn: E3. 
          ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_hit in H16; eauto.
             inversion H16; subst. specialize (H18 y). intuition.
             erewrite <- update_length; eauto. inversion H0; subst.
             apply indexr_var_some' in H24. rewrite H6 in H24; auto.
          ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H16; eauto.
             destruct (x' =? y) eqn: E4.
             -- apply Nat.eqb_eq in E4; subst. erewrite update_indexr_hit in H16; eauto.
                inversion H16. apply indexr_var_some' in H2; auto.
             -- apply Nat.eqb_neq in E4. erewrite update_indexr_miss in H16; eauto.
      * right. destruct H17. exists x0. auto.
Qed.

Lemma update_store_unique_heapOK: forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSUnique) ->
  indexr y σ = Some (TCls c TSUnique, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSUnique) ->
  HeapOK (update (update Γ y (TCls c TSBot)) x (TCls c TSUnique))
  (update (update σ y (TCls c TSBot, & l)) x (TCls c TSUnique, & l)) h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK in *. intuition. destruct (x0 =? x) eqn:E1.
  + apply Nat.eqb_eq in E1; subst. inversion H0; subst. inversion H4. inversion H5; subst.
    erewrite update_indexr_hit. erewrite update_indexr_hit in H18. 3: { rewrite <- update_length. 
    rewrite <- H8. apply indexr_var_some' in H13; auto. } 2: rewrite <- update_length;
    apply indexr_var_some' in H13; auto. inversion H18; subst.
    specialize (H6 x c0 ts). intuition. destruct H9 as [fl [init [ml [oid H9]]]]. 
    exists fl, init, ml, l. intuition. inversion H; intuition. specialize (H22 y c0 TSUnique).
    intuition. destruct H21 as [fl' [init' [ml' [oid' H21]]]]. intuition.
    rewrite H21 in H9; inversion H9; subst. rewrite H22 in H2; inversion H2; subst.
    specialize (H25 f Tf). intuition. destruct H24 as [vf [object H24]]. 
    exists vf, object. intuition. inversion H27; subst. 
    inversion H33; subst. inversion H1; subst. rewrite H42 in H39; inversion H39; subst.  
    econstructor; eauto. inversion H29; subst. 1-3: econstructor; eauto.
    eapply runtime_ty_unique; eauto. intuition.
    - destruct H32. destruct (x0 =? x) eqn:E2.
      * apply Nat.eqb_eq in E2; subst. intros. destruct (x =? y) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. left. exists y. inversion H31. rewrite H32 in H22; 
           inversion H22; subst. econstructor; eauto. erewrite update_indexr_hit; eauto. rewrite <- update_length;
           apply indexr_var_some' in H32; auto. intro. destruct (x' =? y) eqn: E4.
           -- apply Nat.eqb_eq in E4; subst; auto.
           -- apply Nat.eqb_neq in E4. intros. erewrite update_indexr_miss in H34; eauto.
              erewrite update_indexr_miss in H34; eauto.
        ++ apply Nat.eqb_neq in E3. right. intros. destruct H32. destruct (x0 =? x) eqn: E4.
           -- apply Nat.eqb_eq in E4; subst. erewrite update_indexr_hit in H32; eauto.
              inversion H32; subst. inversion H31; subst. specialize (H34 y). intuition.
              rewrite <- update_length. apply indexr_var_some' in H13. rewrite <- H8; auto.
           -- apply Nat.eqb_neq in E4. rewrite update_indexr_miss in H32; auto. destruct (x0 =? y) eqn: E5.
              ** apply Nat.eqb_eq in E5; subst. erewrite update_indexr_hit in H32; subst. inversion H32; subst.
                 apply indexr_var_some' in H22; auto.
              ** apply Nat.eqb_neq in E5. rewrite update_indexr_miss in H32; intuition.
                 destruct H31. specialize (H33 x0); intuition.
      * apply Nat.eqb_neq in E2. destruct (x0 =? y) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. inversion H31. rewrite H32 in H22; inversion H22; subst.
           left. exists x. unfold unique. intuition. erewrite update_indexr_hit; eauto. rewrite <- update_length.
           apply indexr_var_some' in H6; auto. destruct (x' =? x) eqn: E4.
           -- apply Nat.eqb_eq in E4; subst; auto.
           -- apply Nat.eqb_neq in E4. rewrite update_indexr_miss in H34; auto. destruct (x' =? y) eqn: E5.
              ** apply Nat.eqb_eq in E5; subst. erewrite update_indexr_hit in H34; eauto. inversion H34.
                 apply indexr_var_some' in H32; auto.
              ** apply Nat.eqb_neq in E5. rewrite update_indexr_miss in H34; auto. specialize (H33 x').
                 intuition.
        ++ apply Nat.eqb_neq in E3. left. exists x0. unfold unique in *. intuition. rewrite update_indexr_miss; auto.
           rewrite update_indexr_miss; auto. destruct (x' =? x) eqn: E4.
            -- apply Nat.eqb_eq in E4; subst. erewrite update_indexr_hit in H31; eauto. inversion H31; subst.
               specialize (H33 y). intuition. rewrite <- update_length. apply indexr_var_some' in H6; auto.
            -- apply Nat.eqb_neq in E4. rewrite update_indexr_miss in H31; auto. destruct (x' =? y) eqn: E5.
               ** apply Nat.eqb_eq in E5; subst. erewrite update_indexr_hit in H31; eauto. inversion H31.
                  apply indexr_var_some' in H22; auto.
               ** apply Nat.eqb_neq in E5. erewrite update_indexr_miss in H31; auto.
    - right. intros. destruct H31. destruct (x0 =? x) eqn :E2.
      * apply Nat.eqb_eq in E2; subst. erewrite update_indexr_hit in H31. inversion H31; subst.
        assert (exists x : nat, indexr x σ = Some (TCls c TSUnique, & l0)). exists y. auto. 
        eapply H32 in H33. auto. rewrite <- update_length. apply indexr_var_some' in H6; auto.
      * apply Nat.eqb_neq in E2. destruct (x0 =? y) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. erewrite update_indexr_miss in H31; eauto.
           erewrite update_indexr_hit in H31; eauto. inversion H31; subst. apply indexr_var_some' in H22; auto.
        ++ apply Nat.eqb_neq in E3. erewrite update_indexr_miss in H31; eauto.
           erewrite update_indexr_miss in H31; eauto.
  + apply Nat.eqb_neq in E1. destruct (x0 =? y) eqn: E2.
    - apply Nat.eqb_eq in E2; subst. inversion H5; subst.  erewrite update_indexr_miss in H13; eauto.
      erewrite update_indexr_hit in H13; eauto. 2: { inversion H4. rewrite H8. apply indexr_var_some' in H2; auto. }
      inversion H13; subst. contradiction.
    - apply Nat.eqb_neq in E2. repeat erewrite update_indexr_miss; eauto. inversion H5; subst.
      rewrite update_indexr_miss in H13; eauto. rewrite update_indexr_miss in H13; auto.
      assert (tm_has_ty Γ ct $ x0 (TCls c0 ts0)). econstructor; eauto. specialize (H6 x0 c0 ts0).
      intuition. destruct H9 as [fl' [init' [ml' [oid H9]]]]. exists fl', init', ml', oid. intuition.
      specialize (H11 f Tf). intuition. destruct H12 as [vf [object H12]]. exists vf, object.
      intuition. inversion H17; inversion H23; subst. econstructor; eauto. econstructor; eauto.
      rewrite update_indexr_miss; auto. rewrite update_indexr_miss; auto. inversion H19; subst.
      1-3: econstructor; eauto. eapply runtime_ty_unique; eauto. intuition.
      * destruct H22. destruct (x =? y) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. destruct (x1 =? y) eqn: E4.
           -- apply Nat.eqb_eq in E4; subst. left. exists y. unfold unique in *. intuition.
              rewrite H22 in H2; inversion H2; subst. rewrite update_indexr_hit; auto.
              apply indexr_var_some' in H22. rewrite <- update_length; auto. 
              destruct (x' =? y) eqn: E5.
              ** apply Nat.eqb_eq in E5; auto.
              ** apply Nat.eqb_neq in E5. rewrite update_indexr_miss in H21; auto. 
                 rewrite update_indexr_miss in H21; auto.
           -- apply Nat.eqb_neq in E4. left. exists x1. unfold unique in *. intuition.
              erewrite update_indexr_miss; auto. erewrite update_indexr_miss; auto.
              destruct (x' =? y) eqn: E5.
              ** apply Nat.eqb_eq in E5; subst. rewrite update_indexr_hit in H21; auto.
                 inversion H21; subst. specialize (H23 y). intuition. rewrite <- update_length.
                 apply indexr_var_some' in H2; auto.
              ** apply Nat.eqb_neq in E5. rewrite update_indexr_miss in H21; auto. 
                 rewrite update_indexr_miss in H21; auto.
        ++ apply Nat.eqb_neq in E3. destruct (x1 =? x) eqn: E4.
           -- apply Nat.eqb_eq in E4; subst. right. intros. destruct H22. destruct (x1 =? x) eqn: E5.
              ** apply Nat.eqb_eq in E5; subst. erewrite update_indexr_hit in H22; subst.
                 inversion H22; subst. inversion H21. specialize (H24 y). intuition. 
                 rewrite <- update_length. inversion H0; inversion H4; subst. rewrite <- H31.
                 apply indexr_var_some' in H28; auto.
              ** apply Nat.eqb_neq in E5. destruct (x1 =? y) eqn: E6.
                 +++ apply Nat.eqb_eq in E6; subst. rewrite update_indexr_miss in H22; auto.
                     rewrite update_indexr_hit in H22; auto. inversion H22; subst.
                     inversion H21. specialize (H24 y). intuition. apply indexr_var_some' in H2; auto.
                 +++ apply Nat.eqb_neq in E6. rewrite update_indexr_miss in H22; auto.
                     rewrite update_indexr_miss in H22; auto. inversion H21. specialize (H24 x1). intuition.
           -- apply Nat.eqb_neq in E4. left. destruct (x1 =? y) eqn: E5.
              ** apply Nat.eqb_eq in E5; subst. exists x. unfold unique in *. intuition.
                 rewrite H22 in H2; inversion H2; subst. rewrite update_indexr_hit; auto.
                 rewrite <- update_length. inversion H0; inversion H4; subst. rewrite <- H31.
                 apply indexr_var_some' in H28; auto. destruct (x' =? x) eqn: E6.
                 +++ apply Nat.eqb_eq in E6; auto.
                 +++ apply Nat.eqb_neq in E6. destruct (x' =? y) eqn: E7.
                     --- apply Nat.eqb_eq in E7; subst. rewrite update_indexr_miss in H21; auto.
                         rewrite update_indexr_hit in H21; auto. inversion H21. 
                         apply indexr_var_some' in H22; auto.
                     --- apply Nat.eqb_neq in E7. rewrite update_indexr_miss in H21; auto.
                         rewrite update_indexr_miss in H21; auto. specialize (H23 x'). intuition.
              ** apply Nat.eqb_neq in E5. exists x1. unfold unique in *. intuition.
                 rewrite update_indexr_miss; auto. rewrite update_indexr_miss; auto. 
                 destruct (x' =? x) eqn: E6.
                 +++ apply Nat.eqb_eq in E6; subst. rewrite update_indexr_hit in H21; auto. 
                     inversion H21; subst. specialize (H23 y); intuition. rewrite <- update_length.
                     inversion H0; inversion H4; subst. rewrite <- H32. apply indexr_var_some' in H29; auto.
                 +++ apply Nat.eqb_neq in E6. destruct (x' =? y) eqn: E7.
                     --- apply Nat.eqb_eq in E7; subst. rewrite update_indexr_miss in H21; auto.
                         rewrite update_indexr_hit in H21; auto. inversion H21. apply indexr_var_some' in H2; auto.
                     --- apply Nat.eqb_neq in E7. rewrite update_indexr_miss in H21; auto. 
                         rewrite update_indexr_miss in H21; auto.
      * right. intros. destruct H21. destruct (x1 =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. rewrite update_indexr_hit in H21; auto. inversion H21; subst.
           assert (exists x : nat, indexr x σ = Some (TCls c1 TSUnique, & l0)). exists y. intuition.
           apply H22 in H23; auto. rewrite <- update_length. inversion H0; inversion H4; subst.
           rewrite <- H31; apply indexr_var_some' in H28; auto.
        ++ apply Nat.eqb_neq in E3. destruct (x1 =? y) eqn: E4.
           -- apply Nat.eqb_eq in E4; subst. rewrite update_indexr_miss in H21; auto.
              rewrite update_indexr_hit in H21; auto. inversion H21; subst. 
              apply indexr_var_some' in H2; auto.
           -- apply Nat.eqb_neq in E4. rewrite update_indexr_miss in H21; auto.
              rewrite update_indexr_miss in H21; auto. 
              assert (exists x : nat, indexr x σ = Some (TCls c1 TSUnique, & l0)). exists x1.
              intuition. apply H22 in H23; auto.
Qed.

Lemma update_store_unique_heapOK': forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSUnique) ->
  indexr y σ = Some (TCls c TSUnique, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSUnique) ->
  HeapOK' (update (update Γ y (TCls c TSBot)) x (TCls c TSUnique))
  (update (update σ y (TCls c TSBot, & l)) x (TCls c TSUnique, & l)) h ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK' in *. intuition. specialize (H7 o c0 ts0 object).
   intuition. destruct H8 as [fl [init [ml H8]]]. exists fl, init, ml. intuition.
   specialize (H10 f). intuition. destruct H11 as [T [v H11]]. exists T, v. intuition.
   inversion H12; subst. 1-3: econstructor; eauto. eapply runtime_ty_unique; eauto.
   intuition.
   + destruct H17. destruct (x0 =? x) eqn: E1.
     - apply Nat.eqb_eq in E1; subst. destruct (x =? y) eqn: E2.
       * apply Nat.eqb_eq in E2; subst. left. exists y. unfold unique in *. intuition.
         rewrite H17 in H2; inversion H2; subst. erewrite update_indexr_hit; eauto.
         rewrite <- update_length. apply indexr_var_some' in H17; auto. 
         rewrite H17 in H2; inversion H2; subst. destruct (x' =? y) eqn: E3.
         ++ apply Nat.eqb_eq in E3; auto.
         ++ apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H16; auto.
            rewrite update_indexr_miss in H16; auto.
       * apply Nat.eqb_neq in E2. right. intros. destruct H17. destruct (x0 =? x) eqn: E3.
         ++ apply Nat.eqb_eq in E3; subst. rewrite update_indexr_hit in H17; auto.
            inversion H17; subst. inversion H16. specialize (H19 y); intuition.
            apply indexr_var_some' in H17. rewrite <- update_length in H17; auto.
         ++ apply Nat.eqb_neq in E3. destruct (x0 =? y) eqn: E4.
            -- apply Nat.eqb_eq in E4; subst. rewrite update_indexr_miss in H17; auto.
               rewrite update_indexr_hit in H17; inversion H17. apply indexr_var_some' in H2; auto.
            -- apply Nat.eqb_neq in E4. rewrite update_indexr_miss in H17; auto.
               rewrite update_indexr_miss in H17; auto. inversion H16.
               specialize (H19 x0); intuition.
     - apply Nat.eqb_neq in E1. destruct (x0 =? y) eqn: E2.
       * apply Nat.eqb_eq in E2; subst. left. exists x. unfold unique in *. intuition.
         rewrite H17 in H2; inversion H2; subst. rewrite update_indexr_hit; auto.
         inversion H0; inversion H4; subst. rewrite <- update_length; rewrite <- H26.
         apply indexr_var_some' in H23; auto. rewrite H17 in H2; inversion H2; subst.
         destruct (x' =? x) eqn: E3.
         ++ apply Nat.eqb_eq in E3; auto.
         ++ apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H16; auto.
            destruct (x' =? y) eqn: E4.
            -- apply Nat.eqb_eq in E4; subst. rewrite update_indexr_hit in H16; auto.
               inversion H16. apply indexr_var_some' in H17; auto.
            -- apply Nat.eqb_neq in E4. rewrite update_indexr_miss in H16; auto.
               specialize (H18 x'); intuition.
       * apply Nat.eqb_neq in E2. left. exists x0. unfold unique in *. intuition.
         rewrite update_indexr_miss; auto. rewrite update_indexr_miss; auto.
         destruct (x' =? x) eqn: E3.
         ++ apply Nat.eqb_eq in E3; subst. rewrite update_indexr_hit in H16; auto.
            inversion H16; subst. specialize (H18 y); intuition. rewrite <- update_length.
            inversion H0; inversion H4; subst. apply indexr_var_some' in H24; 
            rewrite <- H27; auto.
         ++ apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H16; auto. 
            destruct (x' =? y) eqn: E4.
            -- apply Nat.eqb_eq in E4; subst. rewrite update_indexr_hit in H16. inversion H16.
               apply indexr_var_some' in H2; auto.
            -- apply Nat.eqb_neq in E4. rewrite update_indexr_miss in H16; auto.
   + right. intros. destruct H16. destruct (x0 =? x) eqn: E1.
     - apply Nat.eqb_eq in E1; subst. rewrite update_indexr_hit in H16; auto.
       inversion H16; subst. assert (exists x : nat, indexr x σ = Some (TCls c1 TSUnique, & l0)).
       exists y; auto. apply H17 in H18; auto. rewrite <- update_length.
       inversion H0; inversion H4; subst. rewrite <- H26; apply indexr_var_some' in H23; auto.
     - apply Nat.eqb_neq in E1. rewrite update_indexr_miss in H16; auto. destruct (x0 =? y) eqn: E2.
       * apply Nat.eqb_eq in E2; subst. rewrite update_indexr_hit in H16. inversion H16.
         apply indexr_var_some' in H2; auto.
       * apply Nat.eqb_neq in E2. rewrite update_indexr_miss in H16; auto. 
         assert (exists x : nat, indexr x σ = Some (TCls c1 TSUnique, & l0)). exists x0; auto.
         apply H17 in H18; auto.
Qed.

Lemma update_store_unique_CtxOK: forall {Γ σ h ct x y c ts l}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct $ y (TCls c TSUnique) ->
  indexr y σ = Some (TCls c TSUnique, & l) ->
  value_runtime_ty σ h ct & l (TCls c TSUnique) ->
  CtxOK (update (update Γ y (TCls c TSBot)) x (TCls c TSUnique))
  (update (update σ y (TCls c TSBot, & l)) x (TCls c TSUnique, & l)) h ct.
Proof.
  intros. unfold CtxOK. intuition. eapply update_store_unique_storeOK; eauto.
  eapply update_store_unique_heapOK; eauto. eapply update_store_unique_heapOK'; eauto.
Qed.

Lemma update_load_shared_StoreOK: forall {Γ σ h ct x y c c0 ts l f l0 fs ts0}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct (tfacc $ y f) (TCls c TSShared) ->
  indexr y σ = Some (TCls c0 ts0, & l) ->
  indexr l h = Some (TCls c0 ts0, fs) ->
  indexr f fs = Some (TCls c TSShared, &l0) ->
  value_runtime_ty σ h ct (&l0) (TCls c TSShared) ->
  StoreOK (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, &l0)) h ct.
Proof.
  intros. inversion H. unfold StoreOK in *; intuition. repeat rewrite <- update_length.
  auto. destruct (x0 =? x) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. inversion H0; subst. specialize (H11 x (TCls c ts)). 
    intuition. destruct H11 as [c' [v' H11]]. intuition. inversion H12; subst.
    inversion H0. contradiction. right. rewrite update_indexr_hit in H9; auto.
    all: apply indexr_var_some' in H17 as H17'; auto. inversion H9; subst.
    exists (&l0). intuition. rewrite update_indexr_hit; auto. 
    rewrite <- H8; auto. inversion H5; subst. econstructor; eauto.
    inversion H1; subst. econstructor; eauto. rewrite update_indexr_hit; auto.
    discriminate. inversion H12; subst. inversion H5; subst. exists l0, fs0. intuition. 
    apply indexr_var_some' in H23; auto.
  + apply Nat.eqb_neq in E1. rewrite update_indexr_miss in H9; auto. 
    specialize (H11 x0 Tx). intuition. left. destruct H11 as [c' [v' H11]].
    exists c', v'. intuition. rewrite update_indexr_miss; auto. right.
    destruct H11 as [vx H11]. exists vx.
    intuition. rewrite update_indexr_miss; auto. inversion H13; subst.
    1-3: econstructor; eauto. eapply runtime_ty_unique; eauto. 1: { intuition.
    - destruct H19. destruct (x1 =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. right. intros. destruct H19.
        destruct (x1 =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. rewrite update_indexr_hit in H19.
           inversion H19. inversion H0; subst. apply indexr_var_some' in H25.
           rewrite H8 in H25; auto.
        ++ apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H19; auto.
           inversion H18. specialize (H21 x1); intuition.
      * apply Nat.eqb_neq in E2. left. exists x1. unfold unique in *.
        intuition. rewrite update_indexr_miss; auto. destruct (x' =? x) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. rewrite update_indexr_hit in H18.
           inversion H18. inversion H0; subst. apply indexr_var_some' in H26.
           rewrite H8 in H26; auto.
        ++ apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H18; auto.
    - right. intros. destruct H18. destruct (x1 =? x) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. rewrite update_indexr_hit in H18.
        inversion H18. inversion H0; subst. apply indexr_var_some' in H25.
        rewrite H8 in H25; auto.
      * apply Nat.eqb_neq in E2. rewrite update_indexr_miss in H18; auto.
        assert (exists x : nat, indexr x σ = Some (TCls c1 TSUnique, & l1)).
        exists x1; auto. apply H19 in H20; auto. }
    inversion H14; subst; econstructor; eauto; rewrite update_indexr_miss; auto. 
Qed.

Lemma update_load_shared_HeapOK: forall {Γ σ h ct x y c c0 ts l f l0 fs ts0}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct (tfacc $ y f) (TCls c TSShared) ->
  indexr y σ = Some (TCls c0 ts0, & l) ->
  indexr l h = Some (TCls c0 ts0, fs) ->
  indexr f fs = Some (TCls c TSShared, &l0) ->
  value_runtime_ty σ h ct (&l0) (TCls c TSShared) ->
  HeapOK (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, &l0)) h ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK in *. intuition.
  destruct (x0 =? x) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. inversion H7; subst. rewrite update_indexr_hit in H15.
    2: inversion H0; subst; apply indexr_var_some' in H18; auto. inversion H15; subst.
    specialize (H8 x c1 ts). intuition. destruct H10 as [fl [init [ml [oid H10]]]].
    exists fl, init, ml, l0. intuition. rewrite update_indexr_hit; auto.
    apply indexr_var_some' in H8; auto. unfold HeapOK' in H9. inversion H5; subst.
    specialize (H9 l0 c1 TSShared fs0). intuition. destruct H13 as [fl' [init' [ml' H13]]].
    intuition. rewrite H9 in H10; inversion H10; subst. assert (f0 < length fs0).
    apply indexr_var_some' in H11. rewrite H13 in H11. auto. specialize (H18 f0).
    intuition. destruct H19 as [T [v H19]]. intuition. rewrite H25 in H11; inversion H11; subst.
    exists v, fs0. intuition. econstructor; eauto. 1,2: specialize (StoreOK_wf_ct H6) as Hwf;
    specialize (wf_ct_to_Tf Hwf H9 H25); auto. econstructor; eauto. inversion H20; subst.
    1-3: econstructor; eauto. specialize (StoreOK_wf_ct H6) as Hwf.
    specialize (wf_ct_to_Tf_ts Hwf H9 H25) as Heq. contradiction. 
  + apply Nat.eqb_neq in E1. inversion H7; subst. rewrite update_indexr_miss in H15; auto.
    assert (tm_has_ty Γ ct $ x0 (TCls c1 ts1)). econstructor; eauto. specialize (H8 x0 c1 ts1).
    intuition. destruct H11 as [fl [init [ml [oid H11]]]]. exists fl, init, ml, oid.
    intuition. rewrite update_indexr_miss; auto. specialize (H13 f0 Tf). intuition.
    destruct H14 as [vf [object H14]]. exists vf, object. intuition.
    inversion H19; inversion H25; subst. econstructor; eauto. econstructor; eauto.
    rewrite update_indexr_miss; auto. inversion H21; subst. 1-3: econstructor; eauto.
    specialize (StoreOK_wf_ct H6) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H11 H12) as Heq.
    contradiction. 
Qed.

Lemma update_load_shared_HeapOK': forall {Γ σ h ct x y c c0 ts l f l0 fs ts0}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct (tfacc $ y f) (TCls c TSShared) ->
  indexr y σ = Some (TCls c0 ts0, & l) ->
  indexr l h = Some (TCls c0 ts0, fs) ->
  indexr f fs = Some (TCls c TSShared, &l0) ->
  value_runtime_ty σ h ct (&l0) (TCls c TSShared) ->
  HeapOK' (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, &l0)) h ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK' in *. intros. specialize (H9 o c1 ts1 object).
  intuition. destruct H10 as [fl [init [ml H10]]]. exists fl, init, ml. intuition.
  specialize (H12 f0). intuition. destruct H13 as [T [v H13]]. exists T, v. intuition.
  inversion H14; subst. 1-3: econstructor; eauto. specialize (StoreOK_wf_ct H6) as Hwf.
  specialize (wf_ct_to_Tf_ts Hwf H9 H16) as Heq. contradiction.
Qed.

Lemma update_load_shared_CtxOK: forall {Γ σ h ct x y c c0 ts l f l0 fs ts0}, CtxOK Γ σ h ct -> 
  tm_has_ty Γ ct $ x (TCls c ts) ->
  tm_has_ty Γ ct (tfacc $ y f) (TCls c TSShared) ->
  indexr y σ = Some (TCls c0 ts0, & l) ->
  indexr l h = Some (TCls c0 ts0, fs) ->
  indexr f fs = Some (TCls c TSShared, &l0) ->
  value_runtime_ty σ h ct (&l0) (TCls c TSShared) ->
  CtxOK (update Γ x (TCls c TSShared)) (update σ x (TCls c TSShared, &l0)) h ct.
Proof.
 intros. unfold CtxOK. intuition. eapply update_load_shared_StoreOK; eauto.
 eapply update_load_shared_HeapOK; eauto. eapply update_load_shared_HeapOK'; eauto.
Qed.
 

(* Lemma Progress: forall {Γ σ h ct t T}, tm_has_ty Γ σ h ct t T -> 
  (exists v, value(v) /\ teval t σ h (T, v)).
Proof.
  intros. induction t; inversion H; subst.
    - exists ttrue. intuition. constructor.
    - exists tfalse. intuition. constructor.
    - admit. 
      (* exists(fst (indexr x σ)) . intuition. constructor. auto. *)
    - admit. (* can't get indexr x σ first element.*)
    - admit. (* no def for bvar.*)
    - exists v. intuition. econstructor; intuition; eauto.
Admitted. *)

(* Lemma tm_preservasion: forall {Γ σ h σ' h' ct t T s }, CtxOK Γ σ h ct -> 
  tm_has_ty Γ σ h ct t T -> step s σ h ct σ' h' ->
  tm_has_ty Γ σ' h' ct t T /\ CtxOK Γ σ' h' ct.
Proof.
  intros. induction s.
Admitted.  *)

Lemma update_heap_StoreOK: forall {Γ σ h ct l c T v v' f fs ts}, CtxOK Γ σ h ct ->
  indexr l h = Some ((TCls c ts), fs) -> indexr f fs = Some (T, v') -> value v ->
  value_runtime_ty σ h ct v T ->
  StoreOK Γ σ (update h l ((TCls c ts), update fs f (T, v))) ct.
Proof.
  intros. inversion H. unfold StoreOK in *. intuition. specialize (H9 x Tx). intuition. right.
  destruct H9 as [vx H10]. exists vx. intuition. induction H11; inversion H10; subst.
  1,2: econstructor; eauto. 
  * destruct (l0 =? l) eqn:E1. 
    + apply Nat.eqb_eq in E1; subst. econstructor; eauto. apply indexr_var_some' in H13 as H12'.
      rewrite H13 in H0. inversion H0; subst. erewrite update_indexr_hit; eauto.
    + apply Nat.eqb_neq in E1. econstructor; eauto. 
      rewrite update_indexr_miss. eauto. auto.
  * destruct (l0 =? l) eqn:E1. 
    + apply Nat.eqb_eq in E1; subst. eapply runtime_ty_unique; eauto. 
      apply indexr_var_some' in H13 as H12'. rewrite H13 in H0; inversion H0; subst.
      erewrite update_indexr_hit; eauto.
    + apply Nat.eqb_neq in E1. eapply runtime_ty_unique; eauto.  
      rewrite update_indexr_miss. eauto. auto.
  * induction H11; inversion H10; inversion H13; subst.
    - destruct (l0 =? l) eqn:E1.
      + apply Nat.eqb_eq in E1; subst. rewrite H15 in H0; inversion H0; subst.
        exists l, (update fs f (T, v)). apply indexr_var_some' in H15 as H12'. 
        intuition. erewrite <- update_length; eauto.
        auto. erewrite update_indexr_hit; eauto.
      + apply Nat.eqb_neq in E1. specialize (H14 c0 ts0). intuition. destruct H17 as [l' [fvalues H17]].
        exists l', fvalues. intuition. erewrite <- update_length; eauto. rewrite update_indexr_miss; eauto.
        inversion H17; subst; auto.
    - destruct (l0 =? l) eqn:E1.
      + apply Nat.eqb_eq in E1; subst. rewrite H15 in H0; inversion H0; subst.
        exists l, (update fs f (T, v)). apply indexr_var_some' in H15 as H12'. 
        intuition. 1,3: erewrite <- update_length; eauto.
        auto. all: erewrite update_indexr_hit; eauto.
      + apply Nat.eqb_neq in E1. specialize (H14 c0 TSUnique). intuition; destruct H16 as [l' [fvalues H16]].
        exists l', fvalues. intuition. erewrite <- update_length; eauto. rewrite update_indexr_miss; eauto.
        inversion H16; subst; auto. exists l0, fs0. intuition. erewrite <- update_length. 
        apply indexr_var_some' in H15; auto. erewrite update_indexr_miss; eauto.
Qed. 

Lemma update_heap_HeapOK: forall {Γ σ h ct l c T v v' f fs ts}, CtxOK Γ σ h ct ->
  indexr l h = Some ((TCls c ts), fs) -> indexr f fs = Some (T, v') -> value v ->
  value_runtime_ty σ h ct v T ->
  HeapOK Γ σ (update h l ((TCls c ts), update fs f (T, v))) ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK in *. intuition. specialize (H6 x c0 ts0).
  intuition. destruct H8 as [fl [init [ml [oid H8]]]]. exists fl, init, ml, oid. intuition.
  specialize (H10 f0 Tf). intuition. destruct H11 as [vf [object H11]]. 
  destruct (oid =? l) eqn:E1.
    + apply Nat.eqb_eq in E1; subst. destruct (f0 =? f) eqn:E2.
      - apply Nat.eqb_eq in E2; subst. exists v, (update fs f (T, v)). intuition.
        all: rewrite H10 in H0; inversion H0; subst. all: rewrite H11 in H1; inversion H1; subst.
        erewrite update_indexr_hit; eauto. apply indexr_var_some' in H10; auto.
        erewrite update_indexr_hit; eauto. apply indexr_var_some' in H11; auto.
        induction H3. 1,2: econstructor; eauto. 1,2: destruct (l0 =? l) eqn:E3.
        * apply Nat.eqb_eq in E3; subst.
          rewrite H14 in H10; inversion H10; subst. econstructor; eauto.
          erewrite update_indexr_hit; eauto.
          apply indexr_var_some' in H14 as H14'; eauto.
        * apply Nat.eqb_neq in E3. econstructor; eauto. erewrite update_indexr_miss; eauto.
        * apply Nat.eqb_eq in E3; subst.
          rewrite H14 in H10; inversion H10; subst. eapply runtime_ty_unique; eauto.
          erewrite update_indexr_hit; eauto.
          apply indexr_var_some' in H14 as H14'; eauto.
        * apply Nat.eqb_neq in E3. eapply runtime_ty_unique; eauto. erewrite update_indexr_miss; eauto.
      - apply Nat.eqb_neq in E2. exists vf, (update fs f (T, v)). intuition.
        all: rewrite H10 in H0; inversion H0; subst. erewrite update_indexr_hit; eauto.
        apply indexr_var_some' in H10; auto. rewrite update_indexr_miss; eauto.
        induction H15. 1,2: econstructor; eauto. all: destruct (l0 =? l) eqn:E3.
        * apply Nat.eqb_eq in E3; subst.
          rewrite H15 in H10; inversion H10; subst. econstructor; eauto.
          erewrite update_indexr_hit; eauto.
          apply indexr_var_some' in H15 as H14'; eauto.
        * apply Nat.eqb_neq in E3. econstructor; eauto. erewrite update_indexr_miss; eauto.
        * apply Nat.eqb_eq in E3; subst.
          rewrite H15 in H10; inversion H10; subst. eapply runtime_ty_unique; eauto.
          erewrite update_indexr_hit; eauto.
          apply indexr_var_some' in H15 as H14'; eauto.
        * apply Nat.eqb_neq in E3. eapply runtime_ty_unique; eauto. erewrite update_indexr_miss; eauto.
    + apply Nat.eqb_neq in E1. exists vf, object. intuition. 
      rewrite update_indexr_miss; eauto. apply indexr_var_some' in H8; eauto.
      induction H15. 1,2: econstructor. all: destruct (l0 =? l) eqn:E3.
      * apply Nat.eqb_eq in E3; subst. 
        rewrite H15 in H0; inversion H0; subst. econstructor; eauto.
        erewrite update_indexr_hit; eauto.
        apply indexr_var_some' in H15 as H14'; eauto.
      * apply Nat.eqb_neq in E3. econstructor; eauto. erewrite update_indexr_miss; eauto.
      * apply Nat.eqb_eq in E3; subst. 
        rewrite H15 in H0; inversion H0; subst. eapply runtime_ty_unique; eauto.
        erewrite update_indexr_hit; eauto.
        apply indexr_var_some' in H15 as H14'; eauto.
      * apply Nat.eqb_neq in E3. eapply runtime_ty_unique; eauto. erewrite update_indexr_miss; eauto.
Qed.

Lemma update_heap_HeapOK': forall {Γ σ h ct l c T v v' f fs ts}, CtxOK Γ σ h ct ->
  indexr l h = Some ((TCls c ts), fs) -> indexr f fs = Some (T, v') -> value v ->
  value_runtime_ty σ h ct v T ->
  HeapOK' Γ σ (update h l ((TCls c ts), update fs f (T, v))) ct.
Proof.
  intros. inversion H. intuition. unfold HeapOK' in *. intuition. destruct (o =? l) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. erewrite update_indexr_hit in H5; eauto. inversion H5; subst.
    specialize (H7 l c0 ts0 fs). intuition. destruct H8 as [fl [init [ml H8]]]. exists fl, init, ml.
    intuition. 3: apply indexr_var_some' in H0; eauto. erewrite <- update_length; eauto.
    destruct (f0 =? f) eqn: E2.
      - apply Nat.eqb_eq in E2; subst. exists T, v. intuition. erewrite update_indexr_hit; eauto.
        apply indexr_var_some' in H1; eauto. induction H3; inversion H2; subst. 1,2: econstructor.
        1,2: destruct (l0 =? l) eqn:E3. 
        apply Nat.eqb_eq in E3; subst. econstructor; eauto.
        rewrite H11 in H0; inversion H0; subst. erewrite update_indexr_hit; eauto.
        apply indexr_var_some' in H11 as H11'; eauto.
        apply Nat.eqb_neq in E3. econstructor; eauto.
        rewrite update_indexr_miss; eauto. 
        apply Nat.eqb_eq in E3; subst. eapply runtime_ty_unique; eauto.
        rewrite H11 in H0; inversion H0; subst. erewrite update_indexr_hit; eauto.
        apply indexr_var_some' in H11 as H11'; eauto.
        apply Nat.eqb_neq in E3. eapply runtime_ty_unique; eauto.
        rewrite update_indexr_miss; eauto.
        specialize (H10 f). erewrite <- update_length in H9. intuition. destruct H11 as [T0 [v0 H11]].
        intuition. rewrite H10 in H1; inversion H1; subst. auto.
      - apply Nat.eqb_neq in E2. specialize (H10 f0). erewrite <- update_length in H9. intuition.
        destruct H11 as [T0 [v0 H11]]. exists T0, v0. intuition. rewrite update_indexr_miss; eauto.
        induction H12; inversion H11; subst. 1,2: econstructor; eauto.
        all: destruct (l0 =? l) eqn:E3. 
        apply Nat.eqb_eq in E3; subst. rewrite H13 in H0; inversion H0; subst.
        econstructor; eauto. erewrite update_indexr_hit; eauto. 
        apply indexr_var_some' in H13 as H11'; eauto. apply Nat.eqb_neq in E3.
        econstructor; eauto. rewrite update_indexr_miss; eauto. 
        apply Nat.eqb_eq in E3; subst. rewrite H13 in H0; inversion H0; subst.
        eapply runtime_ty_unique; eauto. erewrite update_indexr_hit; eauto. 
        apply indexr_var_some' in H13 as H11'; eauto. apply Nat.eqb_neq in E3.
        eapply runtime_ty_unique; eauto. rewrite update_indexr_miss; eauto. 
  + apply Nat.eqb_neq in E1. rewrite update_indexr_miss in H5; eauto. specialize (H7 o c0 ts0 object).
    intuition. destruct H8 as [fl [init [ml H8]]]. exists fl, init, ml. intuition.
    specialize (H10 f0). intuition. destruct H11 as [T0 [v0 H11]]. exists T0, v0. intuition.
    induction H12; inversion H11; subst. 1,2: econstructor. all: destruct (l0 =? l) eqn:E3. 
    apply Nat.eqb_eq in E3; subst. rewrite H13 in H0; inversion H0; subst.
    econstructor; eauto. erewrite update_indexr_hit; eauto. apply indexr_var_some' in H13 as H11'; eauto.
    apply Nat.eqb_neq in E3. econstructor; eauto. rewrite update_indexr_miss; eauto.
    apply Nat.eqb_eq in E3; subst. rewrite H13 in H0; inversion H0; subst.
    eapply runtime_ty_unique; eauto. erewrite update_indexr_hit; eauto. apply indexr_var_some' in H13 as H11'; eauto.
    apply Nat.eqb_neq in E3. eapply runtime_ty_unique; eauto. rewrite update_indexr_miss; eauto.
Qed.

Lemma update_heap_CtxOK: forall {Γ σ h ct l c T v v' f fs ts}, CtxOK Γ σ h ct ->
  indexr l h = Some ((TCls c ts), fs) -> indexr f fs = Some (T, v') -> value v ->
  value_runtime_ty σ h ct v T ->
  CtxOK Γ σ (update h l ((TCls c ts), update fs f (T, v))) ct.
Proof.
  intros. unfold CtxOK. intuition. eapply update_heap_StoreOK; eauto.
  eapply update_heap_HeapOK; eauto. eapply update_heap_HeapOK'; eauto.
Qed.

Lemma update_heap_unique_StoreOK: forall {Γ σ h ct y c l fs}, CtxOK Γ σ h ct ->
tm_has_ty Γ ct $ y (TCls c TSUnique) ->
indexr y σ = Some (TCls c TSUnique, & l) ->
indexr l h = Some (TCls c TSUnique, fs) ->
value_runtime_ty σ h ct & l (TCls c TSUnique) ->
StoreOK (update Γ y (TCls c TSBot)) (update σ y (TCls c TSBot, & l)) (update h l (TCls c TSShared, fs)) ct.
Proof.
  intros. inversion H. unfold StoreOK in *. intuition. repeat rewrite <- update_length. auto.
  destruct (x =? y) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. rewrite update_indexr_hit in H7; auto. inversion H7; subst.
    left. exists c, &l. intuition. rewrite update_indexr_hit; auto. all: apply indexr_var_some' in H1; 
    auto; try rewrite H6; auto. 
  + apply Nat.eqb_neq in E1. 
    rewrite update_indexr_miss in H7; auto. specialize (H9 x Tx). intuition.
    destruct H9 as [c' [v' H9]]. left. exists c', v'. intuition. 
    rewrite update_indexr_miss; auto. right. destruct H9 as [vx H9]. exists vx. intuition.
    rewrite update_indexr_miss; auto. inversion H11; subst. 1-2: econstructor; eauto.
    1: { destruct (l =? l0) eqn: E2.
    - apply Nat.eqb_eq in E2; subst. rewrite H15 in H2; inversion H2; subst. contradiction.
    - apply Nat.eqb_neq in E2. econstructor; eauto. rewrite update_indexr_miss; eauto. }
    1: { destruct (l =? l0) eqn: E2.
    - apply Nat.eqb_eq in E2; subst. intuition. destruct H17. inversion H16; intuition.
      all: rewrite H15 in H2; inversion H2; subst.
      specialize (H18 x) as Heq1; intuition. specialize (H18 y); intuition.
      assert (exists x : nat, indexr x σ = Some (TCls c TSUnique, & l0)).
      exists x; auto. apply H17 in H16; auto. contradiction.
    - apply Nat.eqb_neq in E2. eapply runtime_ty_unique; eauto. rewrite update_indexr_miss; eauto.
      intuition.
      * left. destruct H17. inversion H16. specialize (H18 x); intuition; subst.
        exists x. unfold unique in *. intuition. rewrite update_indexr_miss; auto.
        destruct (x' =? y) eqn: E3.
        ++ apply Nat.eqb_eq in E3; subst. rewrite update_indexr_hit in H16; auto. inversion H16.
           apply indexr_var_some' in H1; auto.
        ++ apply Nat.eqb_neq in E3. rewrite update_indexr_miss in H16; auto.
      * right. assert (exists x : nat, indexr x σ = Some (TCls c0 TSUnique, & l0)).
        exists x; auto. apply H17 in H16; auto. }
    subst. inversion H12; subst; econstructor; eauto; rewrite update_indexr_miss; auto.
    subst. specialize (H14 c0 ts). intuition. inversion H11; subst.
    - destruct (l0 =? l) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. inversion H3; subst. contradiction.
        intuition. destruct H14. inversion H14. specialize (H18 x) as Heq1;
        specialize (H18 y). rewrite H21 in H2; inversion H2; subst. intuition.
        assert (exists x : nat, indexr x σ = Some (TCls c TSUnique, & l)).
        exists y; auto. apply H14 in H15; contradiction.
      * apply Nat.eqb_neq in E2. exists l0, fs0. intuition. rewrite <- update_length.
        apply indexr_var_some' in H21; auto. rewrite update_indexr_miss; auto.
    - intuition.
      * destruct (l0 =? l) eqn: E2.
        ++ apply Nat.eqb_eq in E2; subst. destruct H14. inversion H14.
           rewrite H21 in H2; inversion H2; subst.
           specialize (H17 x) as Heq; specialize (H17 y); intuition.
        ++ apply Nat.eqb_neq in E2. exists l0,fs0. intuition.
           rewrite <- update_length; apply indexr_var_some' in H21; auto.
           rewrite update_indexr_miss; auto.
      * assert (exists x : nat, indexr x σ = Some (TCls c0 TSUnique, & l0)). 
        exists x. auto. apply H14 in H15; contradiction.
Qed.


Lemma update_heap_unique_HeapOK: forall {Γ σ h ct y c l fs}, CtxOK Γ σ h ct ->
tm_has_ty Γ ct $ y (TCls c TSUnique) ->
indexr y σ = Some (TCls c TSUnique, & l) ->
indexr l h = Some (TCls c TSUnique, fs) ->
value_runtime_ty σ h ct & l (TCls c TSUnique) ->
HeapOK (update Γ y (TCls c TSBot)) (update σ y (TCls c TSBot, & l)) (update h l (TCls c TSShared, fs)) ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK in *. intuition. destruct (x =? y) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. inversion H5; subst. rewrite update_indexr_hit in H13; auto.
    inversion H13; subst. contradiction. apply indexr_var_some' in H13; rewrite <- update_length in H13; auto.
  + apply Nat.eqb_neq in E1. assert (tm_has_ty Γ ct $ x (TCls c0 ts)). inversion H5; subst.
    rewrite update_indexr_miss in H13; auto. econstructor; eauto.
    specialize (H6 x c0 ts). intuition. destruct H9 as [fl [init [ml [oid H9]]]].
    exists fl, init, ml, oid. intuition. rewrite update_indexr_miss; auto.
    specialize (H11 f Tf). intuition. destruct H12 as [vf [object H12]].
    destruct (oid =? l) eqn: E2.
    - apply Nat.eqb_eq in E2; subst. intuition. rewrite H11 in H2; inversion H2; subst.
      inversion H3; subst. contradiction. intuition.
      * inversion H15. inversion H17. specialize (H20 x) as Heq1. specialize (H20 y) as Heq2.
        intuition.
      * assert (exists x : nat, indexr x σ = Some (TCls c TSUnique, & l)). exists x; auto.
        apply H15 in H17; contradiction.
    - apply Nat.eqb_neq in E2. exists vf, object. intuition. rewrite update_indexr_miss; auto.
      inversion H14; subst. econstructor; eauto. inversion H20; subst. econstructor; eauto.
      rewrite update_indexr_miss; auto. inversion H16; subst. 1-3: econstructor; eauto.
      1: { destruct (l0 =? l) eqn: E3.
      * apply Nat.eqb_eq in E3; subst. rewrite H17 in H2; inversion H2; subst. contradiction.
      * apply Nat.eqb_neq in E3. rewrite update_indexr_miss; eauto. }
      specialize (StoreOK_wf_ct H4) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H9 H10) as Heq.
      contradiction.
Qed.

Lemma update_heap_unique_HeapOK': forall {Γ σ h ct y c l fs}, CtxOK Γ σ h ct ->
tm_has_ty Γ ct $ y (TCls c TSUnique) ->
indexr y σ = Some (TCls c TSUnique, & l) ->
indexr l h = Some (TCls c TSUnique, fs) ->
value_runtime_ty σ h ct & l (TCls c TSUnique) ->
HeapOK' (update Γ y (TCls c TSBot)) (update σ y (TCls c TSBot, & l)) (update h l (TCls c TSShared, fs)) ct.
Proof.
  intros. inversion H; intuition. unfold HeapOK' in *. intuition. destruct (o =? l) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. rewrite update_indexr_hit in H5; inversion H5; subst.
    2: apply indexr_var_some' in H2; auto. specialize (H7 l c0 TSUnique object). intuition.
    destruct H8 as [fl [init [ml H8]]]. exists fl, init, ml. intuition.
    specialize (H10 f). intuition. destruct H11 as [T [v H10]]. intuition.
    inversion H12; subst. 
    - exists TBool, ttrue. intuition. econstructor; eauto.
    - exists TBool, tfalse. intuition. econstructor; eauto.
    - destruct (l0 =? l) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. rewrite H15 in H2; inversion H2; subst; contradiction.
      * apply Nat.eqb_neq in E2. exists (TCls c ts), &l0. intuition. econstructor; eauto.
        rewrite update_indexr_miss; eauto.
    - specialize (StoreOK_wf_ct H4) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H7 H14) as Heq.
      contradiction.
  + apply Nat.eqb_neq in E1. rewrite update_indexr_miss in H5; auto.
    specialize (H7 o c0 ts object). intuition. destruct H8 as [fl [init [ml H8]]].
    exists fl, init, ml. intuition. specialize (H10 f). intuition. 
    destruct H11 as [T [v H11]]. intuition. inversion H12; subst.
    - exists TBool, ttrue. intuition. econstructor; eauto.
    - exists TBool, tfalse. intuition. econstructor; eauto.
    - destruct (l0 =? l) eqn: E2.
      * apply Nat.eqb_eq in E2; subst. rewrite H15 in H2; inversion H2; subst; contradiction.
      * apply Nat.eqb_neq in E2. exists (TCls c1 ts0), &l0. intuition. econstructor; eauto.
        rewrite update_indexr_miss; eauto.
    - specialize (StoreOK_wf_ct H4) as Hwf. specialize (wf_ct_to_Tf_ts Hwf H7 H14) as Heq.
      contradiction.
Qed.

Lemma update_heap_unique_CtxOK: forall {Γ σ h ct y c l fs}, CtxOK Γ σ h ct ->
  tm_has_ty Γ ct $ y (TCls c TSUnique) ->
  indexr y σ = Some (TCls c TSUnique, & l) ->
  indexr l h = Some (TCls c TSUnique, fs) ->
  value_runtime_ty σ h ct & l (TCls c TSUnique) ->
  CtxOK (update Γ y (TCls c TSBot)) (update σ y (TCls c TSBot, & l)) (update h l (TCls c TSShared, fs)) ct.
Proof.
  intros. unfold CtxOK. intuition. eapply update_heap_unique_StoreOK; eauto.
  eapply update_heap_unique_HeapOK; eauto. eapply update_heap_unique_HeapOK'; eauto.
Qed.


(* Lemma update_var_CtxOK: forall {Γ x σ h ct c v ts ts'}, tm_has_ty Γ ct $ x (TCls c ts) ->
  value_runtime_ty σ h ct v (TCls c ts') ->
  CtxOK (update Γ x (TCls c ts')) (update σ x (TCls c ts', v)) h ct. *)

Lemma teval_ends_up_value: forall {t σ h T v}, teval t σ h (T, v) -> 
  value v.
Proof.
  intros. inversion H; subst; try econstructor; eauto.
Qed.

Lemma value_teval: forall {v σ h ct T}, value v -> value_runtime_ty σ h ct v T ->
  teval v σ h (T, v).
Proof.
  intros. induction H; inversion H0; subst; econstructor; eauto.
Qed.

Lemma intersection_length: forall {Γ1 Γ2 Γ'}, intersection Γ1 Γ2 Γ' ->
 length Γ1 = length Γ' /\ length Γ2 = length Γ'.
Proof.
  intros. induction H; try simpl; lia.
Qed.

Lemma intersection_inversion: forall {Γ1 Γ2 Γ' x T}, intersection Γ1 Γ2 Γ' -> indexr x Γ' = Some T ->
  (exists c, indexr x Γ' = Some (TCls c TSBot)) \/ (indexr x Γ' = indexr x Γ1 /\ indexr x Γ' = indexr x Γ2)
.
Proof.
  intros. induction H. 
  + auto.
  + destruct (x =? length Γ') eqn: E1.
    - apply Nat.eqb_eq in E1; subst. right. rewrite indexr_head. 
      specialize (intersection_length H1) as [Heq1 Heq2]. split.
      rewrite <- Heq1. rewrite indexr_head. auto.
      rewrite <- Heq2. rewrite indexr_head; auto.
    - apply Nat.eqb_neq in E1. rewrite indexr_skip in *; auto. intuition. right.
      specialize (intersection_length H1) as [Heq1 Heq2]. split.
      rewrite <- Heq1 in E1. rewrite indexr_skip; auto.
      rewrite <- Heq2 in E1. rewrite indexr_skip; auto.
  + destruct (x =? length Γ') eqn: E1.
    - apply Nat.eqb_eq in E1; subst. right. rewrite indexr_head. 
      specialize (intersection_length H1) as [Heq1 Heq2]. split.
      rewrite <- Heq1. rewrite indexr_head. auto.
      rewrite <- Heq2. rewrite indexr_head; auto.
    - apply Nat.eqb_neq in E1. rewrite indexr_skip in *; auto. intuition. right.
      specialize (intersection_length H1) as [Heq1 Heq2]. split.
      rewrite <- Heq1 in E1. rewrite indexr_skip; auto.
      rewrite <- Heq2 in E1. rewrite indexr_skip; auto.
  + destruct (x =? length Γ') eqn: E1.
    - apply Nat.eqb_eq in E1; subst. right. rewrite indexr_head. 
      specialize (intersection_length H1) as [Heq1 Heq2]. split.
      rewrite <- Heq1. rewrite indexr_head. auto.
      rewrite <- Heq2. rewrite indexr_head; auto.
    - apply Nat.eqb_neq in E1. rewrite indexr_skip in *; auto. intuition. right.
      specialize (intersection_length H1) as [Heq1 Heq2]. split.
      rewrite <- Heq1 in E1. rewrite indexr_skip; auto.
      rewrite <- Heq2 in E1. rewrite indexr_skip; auto.
  + destruct (x =? length Γ') eqn: E1.
    - apply Nat.eqb_eq in E1; subst. left. rewrite indexr_head. exists c; auto.
    - apply Nat.eqb_neq in E1. rewrite indexr_skip in *; auto. intuition. right.
      specialize (intersection_length H1) as [Heq1 Heq2]. split.
      rewrite <- Heq1 in E1. rewrite indexr_skip; auto.
      rewrite <- Heq2 in E1. rewrite indexr_skip; auto.
Qed.


(* Lemma intersection_left_storeOK: forall {Γ1 σ h ct Γ2 Γ'}, intersection Γ1 Γ2 Γ' -> 
  CtxOK Γ1 σ h ct -> StoreOK Γ' σ h ct.
Proof.
  intros. inversion H0. unfold StoreOK in *; intuition. specialize (intersection_length H) as [Heq1 Heq2].
  rewrite <- Heq1. auto. specialize (intersection_inversion H H4) as Heq. intuition.
  + destruct H7 as [c' H7]. left. rewrite H7 in H4; inversion H4; subst.
Admitted.

Lemma intersection_left_heapOK: forall {Γ1 σ h ct Γ2 Γ'}, intersection Γ1 Γ2 Γ' -> 
  CtxOK Γ1 σ h ct -> HeapOK Γ' σ h ct.

Lemma intersection_left_heapOK': forall {Γ1 σ h ct Γ2 Γ'}, intersection Γ1 Γ2 Γ' -> 
  CtxOK Γ1 σ h ct -> HeapOK' Γ' σ h ct.

Lemma intersection_left_CtxOK: forall {Γ1 σ h ct Γ2 Γ'}, intersection Γ1 Γ2 Γ' -> 
  CtxOK Γ1 σ h ct -> CtxOK Γ' σ h ct.

Lemma intersection_right_CtxOK: forall {Γ1 σ h ct Γ2 Γ'}, intersection Γ1 Γ2 Γ' -> 
  CtxOK Γ2 σ h ct -> CtxOK Γ' σ h ct.
Proof.
  intros.  *)

Lemma progress: forall {Γ σ h ct s Γ'}, CtxOK Γ σ h ct -> stmt_has_ty Γ ct s Γ' -> 
  (exists σ' h',  step s σ h ct σ' h' /\ CtxOK Γ' σ' h' ct).
Proof.
  intros. generalize dependent σ. generalize dependent h. induction H0; subst; intros. 
  + (* sskip *)
    exists σ. exists h. intuition. constructor.
  + (* sassgnC *)
    inversion H0; subst. specialize (CtxOK_var_value H1 H0) as [v H4].
    intuition. exists  (update σ x (TBool, v)), h. intuition. constructor; auto.
    inversion H; subst. eapply indexr_var_some' in H9. inversion H1. inversion H3.
    rewrite <- H8; auto. eapply update_store_TBool_CtxOK; eauto.
  + (* sassgnU *)
    inversion H0; subst. specialize (CtxOK_var_value H1 H0) as [v H4].
    intuition. exists  (update (update σ y (TCls c TSBot, v)) x (TCls c TSUnique, v)), h.
    intuition. econstructor; eauto.
    inversion H; subst. eapply indexr_var_some' in H13. inversion H1. inversion H3.
    rewrite <- H10; auto. inversion H7; subst. inversion H5; subst. contradiction.
    eapply update_store_unique_CtxOK; eauto.
  + (* sassgnS *)
    inversion H0; subst. specialize (CtxOK_var_value H1 H0) as [v H4].
    intuition. exists (update σ x (TCls c TSShared, v)), h.
    intuition. eapply step_assgnS; eauto.
    inversion H; subst. eapply indexr_var_some' in H13. inversion H1. inversion H3.
    rewrite <- H10; auto. inversion H5; subst. eapply update_store_shared_CtxOK; eauto. 
  + (* sloadC *)
    specialize (field_acc_type_safety H1 H0) as [v [H2 [H3 H3']]].
    exists (update σ x (TBool, v)), h. inversion H3; subst; intuition. econstructor; eauto. 
    inversion H; subst. apply indexr_var_some' in H7. inversion H1. inversion H4.
    rewrite <- H6; auto. eapply update_store_TBool_CtxOK; eauto. 
  + (* sloadS *)
    specialize (field_acc_type_safety H1 H0) as [v [H2 [H3 H3']]].
    exists (update σ x (TCls c TSShared, v)), h. inversion H3; subst; intuition. econstructor; eauto. 
    inversion H; subst. apply indexr_var_some' in H10. inversion H1. inversion H4.
    rewrite <- H6; auto. inversion H3'; subst. eapply update_load_shared_CtxOK; eauto.
  + (* sstoreC *)
    specialize (field_acc_type_safety H2 H0) as [v [H2' [H3 H3']]]. inversion H3; subst.
    specialize (var_type_safety H2 H1) as [v' H1']. specialize (var_type_safety H2 H) as H10.
    exists σ, (update h l ((TCls c ts), (update fs f (TBool, v')))). intuition.
    all: destruct H10; intuition; rewrite H7 in H8; inversion H8; subst; inversion H16; subst;
    rewrite H23 in H11; inversion H11; subst. econstructor; eauto.
    eapply update_heap_CtxOK; eauto.
  + (* sstoreS *)
    specialize (field_acc_type_safety H2 H0) as [v [H2' [H3 H3']]]. inversion H3; subst.
    specialize (var_type_safety H2 H1) as [v' H1']. specialize (var_type_safety H2 H) as H10.
    exists σ, (update h l ((TCls c ts), (update fs f (TCls c' TSShared, v')))). intuition.
    all: destruct H10; intuition; rewrite H7 in H8; inversion H8; subst; inversion H16; subst;
    rewrite H23 in H11; inversion H11; subst. eapply step_storeS; eauto.
    eapply update_heap_CtxOK; eauto.
  + (* sstoreU *)
    specialize (field_acc_type_safety H2 H0) as [v [H2' [H3 H3']]]. inversion H3; subst.
    specialize (var_type_safety H2 H1) as [v' H1']. specialize (var_type_safety H2 H) as H10. 
    destruct H10; intuition. rewrite H6 in H8; inversion H8; subst. inversion H15; subst. contradiction.
    intuition. 2:{ assert (exists x : nat, indexr x σ = Some (TCls c' TSUnique, & l0)).
    exists y; auto. apply H14 in H19; contradiction. }
    exists (update σ y (TCls c' TSBot, &l0)), (update (update h l0 (TCls c' TSShared, fs0)) l ((TCls c0 TSShared), (update fs f (TCls c' TSShared, &l0)))). 
    intuition. eapply step_storeU; eauto. eapply update_heap_CtxOK; eauto.
    2: { destruct (l =? l0) eqn: E1. 
    - apply Nat.eqb_eq in E1; subst. rewrite H18 in H11; inversion H11; subst.
    - apply Nat.eqb_neq in E1. rewrite update_indexr_miss; auto. }
    2: { econstructor; eauto. rewrite update_indexr_hit; auto. apply indexr_var_some' in H18; auto. discriminate. }
    eapply update_heap_unique_CtxOK; eauto.
  + (* smcallC *)
    specialize (IHstmt_has_ty h σ). intuition. destruct H8 as [σ' [h' [H8 H9]]]. 
    (* need to consider whether change the definition of type inference. *)
    assert (tm_has_ty Γ' ct (t <~ᵗ $ y; $ z) TBool). { induction H3; subst. 1-5: econstructor; eauto. }
    specialize (term_type_safety H9 H3) as H9'. 
    assert ( exists r, teval (t <~ᵗ $y; $z) σ' h' (TBool, r)). { intuition.
      - exists (t <~ᵗ $ y; $ z). inversion H11; rewrite <- H13 in H10;
      inversion H10; subst; try econstructor; eauto. 
      - destruct H11. exists x0. intuition.
    } clear H9'. destruct H11 as [r H11].
    exists (update σ' x (TBool, r)), h'. intuition. 
    inversion H0; subst. inversion H7. inversion H12. intuition.
    specialize (H21 y (TCls c ts)). 1: { intuition.
    - destruct H21 as [c' [v' H21]]. intuition. inversion H15; subst.
      inversion H0; subst. contradiction. 
    - destruct H21 as [vx H21].
      intuition. inversion H21; subst. 1,2: inversion H22.
      econstructor; eauto. inversion H; subst. rewrite <- H14.
      apply indexr_var_some' in H28; auto. inversion H6; subst. 
      all: rewrite <- H14. apply indexr_var_some' in H28; auto.
      apply indexr_var_some' in H26; auto. }
      specialize (term_type_safety' H9 H10) as Htm. destruct Htm as [v Htm].
      intuition. specialize (teval_deterministic H11 H14) as Heq; subst. 
      eapply update_store_TBool_CtxOK; eauto.
      (* induction Tr. induction t0. 
      * admit.
      * econstructor; eauto. inversion H; subst. apply indexr_var_some' in H30; rewrite <- H14; 
        auto. inversion H6; subst. apply indexr_var_some' in H28; rewrite <- H14; auto.
        apply indexr_var_some' in H26; rewrite <- H14; auto.
      * inversion H; subst. contradiction.
      * econstructor; eauto. inversion H; subst. apply indexr_var_some' in H28; rewrite <- H14; 
        auto. inversion H6; subst. apply indexr_var_some' in H28; rewrite <- H14; auto.
        apply indexr_var_some' in H26; rewrite <- H14; auto.
      * inversion H.  *)
    (* induction Tr. induction t0.
    - inversion H10; subst. admit. inversion H19; subst. inversion H7. specialize (StoreOK_wf_ct H21).
      intro. specialize (wf_ct_to_Tf_ts H23 H17 H18) as Heq. contradiction.
    - inversion H10; subst.  
      * rewrite <- H12 in *. specialize (term_type_safety' H9 H10) as Htm. destruct Htm as [v Htm].
        intuition. inversion H16; subst. inversion H15; inversion H11; subst.
        rewrite H34 in H25; inversion H25; subst. eapply update_store_shared_CtxOK; eauto.
      * rewrite <- H12 in *. specialize (term_type_safety' H9 H10) as Htm. destruct Htm as [v Htm].
        intuition. inversion H21; subst. inversion H20; inversion H11; subst.
        rewrite H38 in H26; inversion H26; subst. rewrite H41 in H31; inversion H31; subst.
        rewrite H42 in H32; inversion H32; subst. eapply update_load_shared_CtxOK; eauto.
    - inversion H; subst. contradiction.
    - specialize (term_type_safety' H9 H10) as Htm. destruct Htm as [v Htm].
      intuition. specialize (teval_deterministic H11 H14) as Heq; subst. 
      inversion H4; subst. specialize (update_same H18) as Heq. rewrite Heq.
      eapply update_store_TBool_CtxOK; eauto.
    - inversion H. *)
  + (* smcallS *)
    specialize (IHstmt_has_ty h σ). intuition. destruct H8 as [σ' [h' [H8 H9]]]. 
    assert (tm_has_ty Γ' ct (t <~ᵗ $ y; $ z) (TCls c' TSShared)). { induction H3; subst. 1-5: econstructor; eauto. }
    specialize (term_type_safety H9 H3) as H9'. 
    assert ( exists r, teval (t <~ᵗ $y; $z) σ' h' ((TCls c' TSShared), r)). { intuition.
      - exists (t <~ᵗ $ y; $ z). inversion H11; rewrite <- H13 in H10;
      inversion H10; subst; try econstructor; eauto. 
      - destruct H11. exists x0. intuition.
    } clear H9'. destruct H11 as [r H11].
    exists (update σ' x ((TCls c' TSShared), r)), h'. intuition. 
    inversion H0; subst. inversion H7. inversion H12. intuition.
    specialize (H21 y (TCls c ts)). 1: { intuition.
    - destruct H21 as [c''' [v' H21]]. intuition. inversion H15; subst.
      inversion H0; subst. contradiction. 
    - destruct H21 as [vx H21].
      intuition. inversion H21; subst. 1,2: inversion H22.
      econstructor; eauto. inversion H; subst. rewrite <- H14.
      apply indexr_var_some' in H30; auto. inversion H6; subst. 
      all: rewrite <- H14. apply indexr_var_some' in H28; auto.
      apply indexr_var_some' in H26; auto. }
      specialize (term_type_safety' H9 H10) as Htm. destruct Htm as [v Htm].
      intuition. specialize (teval_deterministic H11 H14) as Heq; subst. 
      inversion H12; subst. 1,2: inversion H15. inversion H10; subst;
      rewrite <- H13 in *. 
      * eapply update_store_shared_CtxOK; eauto. inversion H11; subst; eauto.
      * inversion H11; subst. eapply update_load_shared_CtxOK; eauto.
  + (* smcallU *)
    specialize (IHstmt_has_ty h σ). intuition. destruct H9 as [σ' [h' [H9 H10]]]. 
    assert (tm_has_ty Γ' ct (t <~ᵗ $ y; $ z) (TCls c' TSUnique)). { induction H3; subst. 1-5: econstructor; eauto. }
    specialize (term_type_safety H10 H3) as H9'. 
    assert ( exists r, teval (t <~ᵗ $y; $z) σ' h' ((TCls c' TSUnique), r)). { intuition.
      - exists (t <~ᵗ $ y; $ z). inversion H12; rewrite <- H14 in H11;
      inversion H11; subst; try econstructor; eauto. 
      - destruct H12. exists x0. intuition.
    } clear H9'. destruct H12 as [r H12].
    exists (update (update σ' tx (TCls c' TSBot, r)) x ((TCls c' TSUnique), r)), h'. intuition. 
    inversion H0; subst. inversion H8. inversion H13. intuition.
    specialize (H22 y (TCls c ts)). 1: { intuition.
    - destruct H22 as [c''' [v' H22]]. intuition. inversion H16; subst.
      inversion H0; subst. contradiction. 
    - destruct H22 as [vx H22].
      intuition. inversion H22; subst. 1,2: inversion H23.
      econstructor; eauto. rewrite H7 in H12. inversion H12; subst.
      apply indexr_var_some' in H31; auto. inversion H; subst. all: rewrite <- H15.
      apply indexr_var_some' in H31; auto. inversion H6; subst. 
      apply indexr_var_some' in H29; auto.
      apply indexr_var_some' in H27; auto. }
      specialize (term_type_safety' H10 H11) as Htm. destruct Htm as [v Htm].
      intuition. specialize (teval_deterministic H12 H15) as Heq; subst.
      inversion H13; subst. 1,2: inversion H16. rewrite H7 in *.
      inversion H3; subst. inversion H12; subst.
      eapply update_store_unique_CtxOK; eauto.
  + (* slettmC *)
    specialize (term_type_safety' H3 H0) as Htm. destruct Htm as [v [H6 [H4 H5]]].
    specialize (CtxOK_ext H3 H5 H6 H1) as H7. specialize (IHstmt_has_ty h ((T1, v) :: σ)). intuition.
    destruct H8 as [σ' [h' [H9 H8]]].
    assert (exists σ'' v', σ' = (T1', v') :: σ''). 
    { inversion H8. inversion H10. intuition. specialize (H16 (length Γ') T1').
      assert (indexr (length Γ') (T1' :: Γ') = Some T1'). rewrite indexr_head; auto.
      intuition. 
      + destruct H16 as [c [vx H16]]. intuition. subst.
        exists (delete_nth (length Γ') σ'), vx. assert (length σ' - 1 = length Γ').
        { destruct σ'. inversion H18. simpl. simpl in H12. inversion H12.
        lia. } rewrite <- H16. rewrite <- H16 in H18. erewrite <- transform; eauto.
      + destruct H16 as [vx H16]. intuition. exists (delete_nth (length Γ') σ'), vx.
        assert (length σ' - 1 = length Γ'). { destruct σ'. inversion H17. simpl.
        simpl in H12. inversion H12. lia. } rewrite <- H20. rewrite <- H20 in H17.
        erewrite <- transform; eauto. } 
    destruct H10 as [σ'' [v' H10]]. subst. exists σ'', h'. intuition.
    inversion H3. inversion H10. rewrite H12 in H9; eauto. econstructor; eauto.
    specialize (CtxOK_trim H8); auto.
  + (* slettmU *)
  specialize (term_type_safety' H2 H0) as Htm. destruct Htm as [v [H6 [H4 H5]]].
  specialize (CtxOK_ext_unique H2 H4 H5 H0) as H7. 
  specialize (IHstmt_has_ty h ((TCls c TSUnique, v) :: update σ x (TCls c TSBot, v))). 
  intuition. destruct H3 as [σ' [h' [H9 H8]]].
  assert (exists σ'' v', σ' = (T1', v') :: σ''). 
  { inversion H8. inversion H3. intuition. specialize (H15 (length Γ') T1').
    assert (indexr (length Γ') (T1' :: Γ') = Some T1'). rewrite indexr_head; auto.
    intuition. 
    + destruct H15 as [c' [vx' H15]]. intuition. subst.
      exists (delete_nth (length Γ') σ'), vx'. assert (length σ' - 1 = length Γ').
      { destruct σ'. inversion H17. simpl. simpl in H11. inversion H11.
      lia. } rewrite <- H15. rewrite <- H15 in H17. erewrite <- transform; eauto.
    + destruct H15 as [vx H15]. intuition. exists (delete_nth (length Γ') σ'), vx.
      assert (length σ' - 1 = length Γ'). { destruct σ'. inversion H16. simpl.
      simpl in H11. inversion H11. lia. } rewrite <- H19. rewrite <- H19 in H16.
      erewrite <- transform; eauto. } 
  destruct H3 as [σ'' [v' H10]]. subst. exists σ'', h'. intuition.
  inversion H2. inversion H3. rewrite H11 in H9; eauto. eapply step_lettmU; eauto.
  specialize (CtxOK_trim H8); auto.
  + (* sletnew *)
    specialize (termlist_type_safety H0 H3) as Hobj. destruct Hobj as [objrec Hobj]. intuition.
    specialize (IHstmt_has_ty ((TCls c ts, objrec) :: h) ((TCls c ts, & (length h)) :: σ)).
    eapply CtxOK_heap_ext in H0 as H''; eauto. 
    assert (value_runtime_ty σ ((TCls c ts, objrec) :: h) ct &(length h) (TCls c ts)).
    { induction ts. eapply runtime_ty_unique; eauto. eapply indexr_var_some' in H; auto.
      rewrite indexr_head; auto. right. unfold not. intros. destruct H7.
      inversion H0. inversion H8. intuition. apply indexr_var_some' in H7 as Heq.
      rewrite <- H10 in Heq. apply indexr_var_some in Heq. destruct Heq.
      specialize (H14 x x0). intuition. destruct H14 as [c' [v' H14]]. intuition.
      rewrite H16 in H7; inversion H7. destruct H14 as [vx H14]. intuition.
      rewrite H15 in H7; inversion H7; subst. specialize (H19 c TSUnique).
      intuition. destruct H18 as [l [fvalues H18]]. intuition. inversion H18; subst.
      lia. all: econstructor. 1,4: eapply indexr_var_some' in H as H0'; auto.
      2,4: discriminate. all: eapply indexr_head. } assert (value & (length h)) by auto.
    induction ts. 
    1: { specialize (CtxOK_ext_unique_pure H0 H'') as H'''. intuition. destruct H9 as [σ' [h' H9]].
    intuition. assert (exists σ'' v', σ' = (TCls c ts', v') :: σ'').
    { inversion H11. inversion H9. intuition. specialize (H17 (length Γ') (TCls c ts')).
      rewrite indexr_head in H17. intuition. 
      + destruct H17 as [c' [v' H17]]. intuition. inversion H14; subst. 
        exists (delete_nth (length Γ') σ'), v'. intuition. 
        assert(length σ' - 1 = length Γ').
        { destruct σ'. inversion H18. simpl. simpl in H13. inversion H13. lia. } 
        rewrite <- H17. erewrite <- transform; eauto.
        rewrite <- H17 in H18; auto.
      + destruct H17 as [v' H17]. intuition. 
        exists (delete_nth (length Γ') σ'), v'. intuition. 
        assert(length σ' - 1 = length Γ').
        { destruct σ'. inversion H14. simpl. simpl in H13. inversion H13. lia. } 
        rewrite <- H20. erewrite <- transform; eauto.
        rewrite <- H20 in H14; auto.
    } destruct H9 as [σ'' [v' H9]]. subst. exists σ'', h'.
    specialize (CtxOK_trim H11). intuition. econstructor; eauto.
    (* specialize (termlist_type_safety H H3)as H10. destruct H10 as [o1 H10].
    erewrite varlist_eval_deterministic; eauto. *)
    1,2: inversion H0; inversion H12. rewrite <- H14; auto. intros.
    rewrite H14 in H10; eauto. } 
    1: { assert ((forall c0 : cn, TCls c TSShared <> TCls c0 TSUnique)). intuition; inversion H9.
    specialize (CtxOK_ext H'' H7 H8 H9) as H'. intuition. destruct H10 as [σ' [h' H10]].
    intuition. assert (exists σ'' v', σ' = (TCls c ts', v') :: σ'').
    { inversion H12. inversion H10. intuition. specialize (H18 (length Γ') (TCls c ts')).
      rewrite indexr_head in H18. intuition. 
      + destruct H18 as [c' [v' H18]]. intuition. inversion H15; subst. 
        exists (delete_nth (length Γ') σ'), v'. intuition. 
        assert(length σ' - 1 = length Γ').
        { destruct σ'. inversion H19. simpl. simpl in H14. inversion H14. lia. } 
        rewrite <- H18. erewrite <- transform; eauto.
        rewrite <- H18 in H19; auto.
      + destruct H18 as [v' H18]. intuition. 
        exists (delete_nth (length Γ') σ'), v'. intuition. 
        assert(length σ' - 1 = length Γ').
        { destruct σ'. inversion H15. simpl. simpl in H14. inversion H14. lia. } 
        rewrite <- H21. erewrite <- transform; eauto.
        rewrite <- H21 in H15; auto.
    } destruct H10 as [σ'' [v' H10]]. subst. exists σ'', h'.
    specialize (CtxOK_trim H12). intuition. econstructor; eauto.
    (* specialize (termlist_type_safety H H3)as H10. destruct H10 as [o1 H10].
    erewrite varlist_eval_deterministic; eauto. *)
    1,2: inversion H0; inversion H13. rewrite <- H15; auto. intros.
    rewrite H15 in H11; eauto. }   (* varlist_has_type_closed *)
    assert ((forall c0 : cn, TCls c TSBot <> TCls c0 TSUnique)). intuition; inversion H9.
    specialize (CtxOK_ext H'' H7 H8 H9) as H'. intuition. destruct H10 as [σ' [h' H10]].
    intuition. assert (exists σ'' v', σ' = (TCls c ts', v') :: σ'').
    { inversion H12. inversion H10. intuition. specialize (H18 (length Γ') (TCls c ts')).
      rewrite indexr_head in H18. intuition. 
      + destruct H18 as [c' [v' H18]]. intuition. inversion H15; subst. 
        exists (delete_nth (length Γ') σ'), v'. intuition. 
        assert(length σ' - 1 = length Γ').
        { destruct σ'. inversion H19. simpl. simpl in H14. inversion H14. lia. } 
        rewrite <- H18. erewrite <- transform; eauto.
        rewrite <- H18 in H19; auto.
      + destruct H18 as [v' H18]. intuition. 
        exists (delete_nth (length Γ') σ'), v'. intuition. 
        assert(length σ' - 1 = length Γ').
        { destruct σ'. inversion H15. simpl. simpl in H14. inversion H14. lia. } 
        rewrite <- H21. erewrite <- transform; eauto.
        rewrite <- H21 in H15; auto.
    } destruct H10 as [σ'' [v' H10]]. subst. exists σ'', h'.
    specialize (CtxOK_trim H12). intuition. econstructor; eauto.
    (* specialize (termlist_type_safety H H3)as H10. destruct H10 as [o1 H10].
    erewrite varlist_eval_deterministic; eauto. *)
    1,2: inversion H0; inversion H13. rewrite <- H15; auto. intros.
    rewrite H15 in H11; eauto. 
  + (* sif *)
    specialize (IHstmt_has_ty1 h σ). specialize (IHstmt_has_ty2 h σ).
    intuition. destruct H1 as [σ1 [h1 H1]]; destruct H2 as [σ2 [h2 H2]].
    inversion H; subst. specialize (CtxOK_var_value H0 H) as H4'.
    destruct H4' as [v H4']. intuition. specialize (term_type_safety' H0 H) as H11.
    destruct H11 as [v' [H11 [H11' H11'']]]. inversion H0. inversion H7.
    inversion H11; subst; inversion H11''; subst.
    - exists σ1, h1. intuition. econstructor; eauto. rewrite <- H12.  
      specialize (stmt_has_ty_closed H0_0) as Hcl. auto.
    - exists σ2, h2. intuition. eapply step_if_false; eauto. 
      rewrite <- H12. specialize (stmt_has_ty_closed H0_) as Hcl. auto.
  + (* sloop *)
    specialize (IHstmt_has_ty h σ).
    intuition. destruct H5 as [σ' [h' [H5 H5']]].
    specialize (term_type_safety' H4 H) as H11. intuition. destruct H11 as [v [H6 H6']].
    inversion H6; subst. 
    (* 3 cases for the evaluation of x: ttrue, tfalse and object address*)
    - exists σ', h'. intuition. econstructor; eauto. 
    - exists σ, h. intuition. apply step_loop_false; auto.
    - inversion H; subst. specialize (CtxOK_var_value H4 H) as H7'.
      destruct H7' as [v H7]. intuition. inversion H9; subst.
  + (* sseq *)
    specialize (IHstmt_has_ty1 h σ). 
    intuition. destruct H1 as [σ1 [h1 [H2 H2']]].
    specialize (IHstmt_has_ty2 h1 σ1). intuition. destruct H1 as [σ' [h' [H3 H3']]].
    exists σ', h'. intuition. econstructor; eauto. inversion H0.
    inversion H1. rewrite <- H5; auto.
Qed.

 (* need a main expression
Theorem type_safety: forall {Γ σ h ct s},
    stmt_has_ty Γ σ h ct s TUnit -> CtxOK Γ σ h ct -> (
    exists σ' h' Γ',  step s σ h ct σ' h' /\ CtxOK Γ' σ' h' ct
)
.
Proof. 
  intros Γ σ h ct s H HCT.
  specialize (stmt_has_ty_closed H) as Hcl. 
  (* induction H; subst.
  + exists σ. exists h. exists Γ. intuition. constructor.
  + inversion H0; subst. specialize (CtxOK_var_value HCT H2). intuition.
    destruct H1 as [v H1']. intuition. exists  (update σ x (T, v)). exists h. exists Γ.
    intuition. constructor; auto. inversion H; subst. eapply indexr_var_some' in H5.
    inversion HCT. inversion H4. rewrite <- H8. auto. eapply update_store_CtxOK; eauto.
    inversion H; subst; auto. inversion HCT. inversion H4. intuition. specialize (H10 y T).
    intuition. destruct H8 as [v' H8]. intuition. rewrite H10 in H1. inversion H1; subst. auto. 
  + specialize (field_acc_type_safety HCT H0). intuition. destruct H1 as [v H1].
    intuition. exists (update σ x (T, v)). exists h. exists Γ. 
    inversion H0; inversion HCT; subst. unfold HeapOK in H15. specialize (H15 y c).
    intuition; destruct H1 as [fl [init [ml [oid H1]]]]; intuition; specialize (H8 f T);
    intuition; destruct H9 as [vf [object H9]]; intuition; inversion H3; subst; 
    rewrite H20 in H4; inversion H4; subst;
    rewrite H23 in H8; inversion H8; subst; rewrite H24 in H9; inversion H9; subst.
    econstructor; eauto.
    intuition; inversion H; subst; eapply indexr_var_some' in H17. inversion H14.
    rewrite <- H15. auto. eapply update_store_CtxOK; eauto. inversion H; subst; auto.
  + specialize (field_acc_type_safety HCT H) as H'. destruct H' as [v H'].
    inversion H; subst. specialize (var_type_safety HCT H0) as H0'.
    destruct H0' as [v' H0']. intuition. inversion H2; subst.
    exists σ. exists (update h l ((TCls c0), (update fs f (T, v')))). exists Γ. intuition.
    econstructor; eauto. eapply update_heap_CtxOK; eauto.
  + admit.
  + specialize (CtxOK_ext HCT H1 H2). intro. specialize (stmt_has_ty_closed H3) as H3'.
    intuition. destruct H6 as [σ' [h' [Γ' H6]]]. exists σ'. exists h'. exists Γ'.  
    intuition.  *)


       generalize dependent σ. generalize dependent h.
       generalize dependent Γ.
       induction s; intros; subst; inversion H; subst.
    + (* sskip *) 
      exists σ. exists h. exists Γ. intuition.
      constructor.
    + (* sassign *)
      inversion H7.  subst. 
      specialize (CtxOK_var_value HCT H1). intuition.
      destruct H0 as [v H0']. intuition.
      exists  (update σ x (T, v)). exists h. exists Γ.  intuition.
      constructor; auto. inversion Hcl; inversion H10; subst.
      inversion HCT. inversion H3. rewrite <- H5; auto.
      eapply update_store_CtxOK; eauto. inversion H6. intuition.
      inversion HCT. inversion H3. intuition. specialize(H11 y T).
      intuition. destruct H9 as [v' H9]. intuition. rewrite H11 in H0.
      inversion H0. subst. intuition. 
    + (* sload *)
      specialize (field_acc_type_safety HCT H8). intuition.
      destruct H0 as [v H0']. intuition.  
      exists  (update σ x (T, v)). exists h. exists Γ. intuition.
      inversion H1. subst.
      specialize (field_acc_type_safety HCT H8). intuition.
      econstructor; eauto. inversion Hcl; inversion H10; subst.
      inversion HCT. inversion H3. rewrite <- H5; auto.
      eapply update_store_CtxOK; eauto.
      inversion H6. intuition. inversion H1; subst. inversion HCT.
      inversion H8; subst. unfold HeapOK in H3. specialize (H3 y c0).
      intuition. destruct H4 as [fl [init [ml [oid H4]]]]. intuition.
      rewrite H3 in H7. inversion H7. subst. specialize (H14 f T).
      intuition. destruct H15 as [vf [object H15]]. intuition.
      rewrite H14 in H11; inversion H11; subst. rewrite H15 in H12.
      inversion H12; subst. intuition.  
    + (* sstore *)
      specialize (field_acc_type_safety HCT H6) as H'. 
      destruct H' as [vf H'']. intuition.
      inversion H1; subst.
      specialize (var_type_safety HCT H8) as H8'.
      destruct H8' as [vy H8'']. intuition.
      exists σ. exists (update h l ((TCls c), (update fs f (T, vy)))). exists Γ. intuition.
      econstructor; eauto. eapply update_heap_CtxOK; eauto.
    + (* smcall *)
       specialize (var_obj_type_safety HCT H9) as H1. 
       destruct H1 as [l [H1 [H2 H3]]]. 
       esplit; esplit; esplit. split. econstructor. 
       (* eauto will misapply H1 and fix the return value to oid. so I manualy apply here. *) 
       eapply H2. eapply H10. eapply H11.
      admit. admit. 1-2: try inversion H4; inversion H12; subst; apply indexr_var_some' in H5, H17;
      inversion HCT; inversion H0; rewrite <- H7; auto. 
      admit.  (* here seems to need a hypothesis about the step change of method
      (which is step s σ h ct σ' h' and teval t  σ' h' (Tr, & l))
      and we need to prove that opening operation won't change *)
    + (* slettm *)
    (* need to use IHs to get the state after step s, and set the target state as
    value of t0 :: the result state from step s *)
    (* need proof: progress, ctxok_ext. stmt_has_ty need reconsider if it need to 
    maintain the same length of env(Γ) and store(σ). *)
      (* rename t into T. specialize (IHs (T:: Γ)).
      apply stmt_has_ty_closed in H9 as Hcl1. intuition.
      apply Progress in H8 as Hp. destruct Hp as [v [Hv1 Hv2]].
      specialize (H0 h ((T, v) :: σ)). assert (stmt_has_ty (T :: Γ) ((T, v) :: σ) h ct s TUnit).
      { admit. } (* its like a weakening lemma here but with the inconsistency between Γ and σ. *) 
      (* specialize (CtxOK_ext HCT H8 Hv2) as HCT'. intuition.
      destruct H0 as [σ' [h' [Γ' [H01 H02]]]]. exists σ', h', Γ'.
      intuition. econstructor; eauto. erewrite closed_stmt_open_id; eauto. (* may not be right*)
      inversion HCT; inversion H0; rewrite H3 in H7; auto. *)*) 
      admit. 
    + (* sletnew *)
      specialize (IHs ((TCls c) :: Γ)). intuition. apply stmt_has_ty_closed in H12 as Hcl'.
      intuition. (* need a progress lemma stating that if l have type TS,
      then they will definitely eval into list of values.*)
      (* specialize (H0 (((TCls c), objrec) ::h) (((&(length σ))):: σ)). *)
      admit.
    + (* sif *)
      apply stmt_has_ty_closed in H8 as Hcl1.
      apply stmt_has_ty_closed in H9 as Hcl2.
      specialize (IHs1 Γ). intuition. specialize (IHs2 Γ). intuition.
      specialize (H0 h σ). intuition. specialize (H1 h σ). intuition.
      inversion H7; subst. specialize (CtxOK_var_value HCT H3) as H2. 
      destruct H2 as [v [H2 H2']]. intuition.
      specialize (term_type_safety HCT H7) as H4. intuition. inversion H5.
      destruct H5 as [v' [H5 H5']]. inversion H5; subst. 
      (* induction on value of guard *)
      - destruct H0 as [σ1[h1[Γ1 [H01 H02]]]].
      exists σ1,h1,Γ1. intuition. eapply step_if_true. intuition. intuition.
      inversion HCT; inversion H0; rewrite H6 in Hcl2; auto.
      - destruct H1 as [σ2[h2[Γ2 [H21 H22]]]].
      exists σ2,h2,Γ2. intuition. eapply step_if_false. intuition. intuition.
      inversion HCT; inversion H1; rewrite H6 in Hcl1; auto.
      (* if x is evalued into an oid *)
      - inversion H5'; subst. inversion HCT. inversion H4. intuition.
      specialize (H16 x TBool). intuition. destruct H12 as [vx H12]. intuition.
      rewrite H16 in H14. inversion H14. subst. inversion H17.
    + (* sloop *)
      apply stmt_has_ty_closed in H7 as Hcl1.
      specialize (IHs Γ). intuition. specialize (H0 h σ). intuition.
      inversion H6; subst. specialize (term_type_safety HCT H6) as H1. intuition.
      inversion H3. destruct H3 as [v [H1 H1']]. inversion H1; subst. 
      destruct H0 as [σ'[h'[Γ' [H01 H02]]]]. exists σ',h',Γ'. intuition.
      eapply step_loop_true. intuition. eapply H01. admit.
      (* we should also have a hypothesis about step sloop here start from the state of σ',h',Γ'. *)
      destruct H0 as [σ'[h'[Γ' [H01 H02]]]]. exists σ',h',Γ'. intuition.
      eapply step_loop_false. intuition. intuition.
      inversion H1'; subst. inversion HCT. inversion H3. intuition.
      specialize (H13 x TBool). intuition. destruct H8 as [vx H8]. intuition.  
      rewrite H13 in H11. inversion H11. subst. inversion H14.
    + (* sseq *)
      specialize (IHs1 Γ). apply stmt_has_ty_closed in H2 as H2'. intuition. 
      specialize (H0 h σ). intuition. destruct H0 as [σ'' [h'' [Γ'' [H0 H1]]]].
      specialize (IHs2 Γ''). assert ( closed_stmt 0 (length Γ'') s2 ).
      { eapply closed_stmt_monotone; eauto. assert (length σ <= length σ'').
        eapply step_extend_store; eauto. inversion H1. inversion H4; subst.
        rewrite H6. inversion HCT. inversion H10. rewrite H12. lia. }
      intuition. specialize (H4 h'' σ''). specialize (H7 Γ'' σ'' h'').
      intuition. destruct H4 as [σ' [h' [Γ' [H11 H12]]]]. 
      exists σ'; exists h';exists Γ'. intuition. econstructor; eauto.
      inversion HCT; inversion H4. rewrite H7 in H8; auto.
  Admitted.   

 *)
