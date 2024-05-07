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

Inductive ts: Type := 
(* | TSTop : ts *)
| TSUnique : ts
| TSShared : ts
| TSBot : ts
.

Inductive ty: Type :=
| TCls   : cn -> ts -> ty
| TBool  : ty
| TACls  : cn -> ts -> ts -> ty
(* | TUnit  : ty *)
(* | TFun   : ty -> ty -> ty *)
.

 (* expression *) 
Inductive tm : Type :=
  | ttrue:  tm                (* true *)
  | tfalse: tm                (* false *)
  | tvar :  var -> tm         (* x *)
  | tfacc:  var ->  f -> tm   (* x.f *)

(* runtime expression *)
  | toid: l -> tm   
  | toidfacc: l -> f -> tm
.  

(* concrete state (of object). *)
Inductive cs : Type := 
| CSunique: cs
| CSshared: cs
.


Notation "& l"   := (toid l) (at level 0, right associativity).
Coercion tvar : var >-> tm. (* lightens the notation of term variables *)

(* value *)
Inductive value : tm -> Prop :=
  | vtrue : value (ttrue)
  | vfalse: value (tfalse) 
  | void:   forall o, value (& o)
. 


#[global] Hint Constructors value : core.

(* statement *)
Inductive stmt : Type :=
  | sskip   : stmt                                          (* skip *)
  | sassgn  : var -> var -> stmt                            (* x := y *)
  | sload   : var -> var -> f -> stmt                       (* x := y.f *)
  | sstore  : var -> f -> var -> stmt                       (* x.f := y *)
  | smcall  : var -> var -> m -> var -> stmt                (* x := y.m (z) *) (* receivier is implicit passed *) (* method m1 (z: C, x: int, ret: T) { *)
  | slettm  : (* var ->  *) ty -> tm -> stmt -> stmt        (* var x : T = e in S *)  (* bound variable is implicit *)
  | sletnew : (* var ->  *) ty -> ty -> list var -> stmt -> stmt   (* var x : C = new C (list of p) in S *)  (* bound variable is implicit *)
  | sif     : var -> stmt -> stmt -> stmt                   (* if x then s1 else s2 *)
  | sloop   : var -> nat -> nat -> stmt -> stmt             (* while x  do S *)
  | sseq    : stmt -> stmt -> stmt                          (* s1; s2 *)
.
Module LangNotations.
  Declare Scope lang.
Notation "x [:=] y" := (sassgn $x $y) (at level 75, no associativity) : lang.
Notation "x [:=] y ~ f" := (sload $x $y f) (at level 75, no associativity) : lang.
Notation "x ~ f [:=] y" := (sstore $x f $y) (at level 75, no associativity) : lang.
Notation "x [:=] y ~ m  ( z )" := (smcall $x $y m $z) (at level 75, no associativity) : lang. 
Notation "'let x'  T  [:=] t 'in' s" := (slettm T t s) (at level 75, no associativity) : lang. 
Notation "'let x' : cn [:=] cn1 ( list y ) 'in' s" := (sletnew cn cn1 tm (list $y) s) (at level 75, no associativity) : lang.
Notation "'if' x 'then' s1 'else' s2" := (sif $x s1 s2) (at level 75, no associativity) : lang.
Notation "'while' x c l s" := (sloop $x c l s) (at level 75, no associativity) : lang.
Notation "s1 ; s2" := (sseq s1 s2) (at level 75, no associativity) : lang. 
End LangNotations.

(*
Inductive field_decl : Type :=
  | f_decl: ty -> field_decl
.
*)

(* def m(x: T, ... ) : ret : T = { S } *)
(* indexed by method name in the meth_decl list *)  (* need well-formed check*)
Inductive meth_decl: Type :=
  | m_decl : (* ty -> *) ty ->  ty -> stmt -> tm -> meth_decl   (* one parameter method; return tm *)
                                                                (* receiver's type is implicit *)
. 

Inductive constructor_decl: Type :=  (* receiver's type and return type are implicit *)
  | init_decl : (* ty -> *) list ty (*  parameter *) -> (* ty -> *) stmt -> tm -> constructor_decl
.

Inductive class: Type :=
  | cls_object: class                                               (* class Object*)
  | cls_def: (* list of fields type*) (list ty) -> constructor_decl -> (list meth_decl) -> class  
  .
 
(* the index is the defining class name *)  
Definition class_table := list class. 
Inductive wf_constructor : list ty (* fields ty *) -> (constructor_decl ) -> Prop :=
  | wf_init: forall fds stmt tm,
    wf_constructor fds (init_decl fds stmt tm)
.


Inductive wf_ty: ty -> class_table -> Prop :=
  (* | wf_TBot : forall ct,
     wf_ty TBot ct  
  | wf TTop : forall ct,
    wf_ty TTop ct *)
  | wf_TCls : forall c ct cd ts,
    indexr c ct = Some cd ->
    wf_ty (TCls c ts) ct
  | wf_Bool:  forall ct,
    wf_ty TBool ct
  (* | wf_TUnit: forall ct,
    wf_ty TUnit ct *)
.
#[global] Hint Constructors wf_ty : core.

(* used in wf_ct *)
Inductive wf_normal_ty : ty -> class_table -> Prop :=
 | wf_p_Tcls : forall c ct ts, 
   wf_ty (TCls c ts) ct ->
   ts <> TSBot ->
   wf_normal_ty (TCls c ts) ct
 | wf_p_Bool:  forall ct,
   wf_normal_ty (TBool) ct
. 
#[global] Hint Constructors wf_normal_ty : core.


Inductive wf_field_decl: list ty -> class_table -> Prop :=
| wf_field_decl_nil: forall ct,
  wf_field_decl [] ct
| wf_field_decl_cons: forall ct T tail,
  wf_normal_ty T ct ->
  (forall c ts, T = TCls c ts -> ts = TSShared) ->
  wf_field_decl tail ct ->
  wf_field_decl ( T :: tail) ct
.
#[global] Hint Constructors wf_field_decl : core.

Inductive wf_meth_decls: list meth_decl -> class_table -> Prop :=
  | wf_meth_decls_nil: forall ct,
    wf_meth_decls [] ct
  | wf_meth_decls_cons: forall Tp Tr s t tail ct,
    wf_normal_ty Tp ct ->
    wf_normal_ty Tr ct ->
    wf_meth_decls tail ct ->
    wf_meth_decls ((m_decl Tp Tr s t):: tail) ct
.
#[global] Hint Constructors wf_meth_decls : core.

(* check inheritance;  *)
Inductive wf_ct : class_table -> Prop :=
  | wf_ct_nil : wf_ct [] 
  (* | wf_ct_obj :
      wf_ct  [cls_object ] *)
  | wf_ct_cons: forall  ct init fl ml,
      wf_ct ct ->
      wf_meth_decls ml ct ->
      wf_field_decl fl ct ->             (* well-formed method declration: types *)
      wf_ct  ((cls_def fl init ml) :: ct)   (* list grows to the left *)
.  
#[global] Hint Constructors wf_ct : core.

Lemma wf_ct_inversion: forall{c ct}, wf_ct (c::ct) -> wf_ct ct.
Proof. intros. inversion H. subst. auto.
Qed. 

Lemma wf_hit: forall {c ct}, wf_ct ct -> c < length ct ->
  (exists init fl ml, indexr c ct = Some (cls_def fl init ml)).
Proof.
  intros. induction H. inversion H0. destruct (c =? length ct) eqn: E1.
  + apply Nat.eqb_eq in E1. subst. exists init, fl, ml. apply indexr_head.
  + apply Nat.eqb_neq in E1. assert (length (cls_def fl init ml :: ct) = S (length ct)) by auto.
    rewrite H3 in H0. assert (c < length ct) by lia. intuition. destruct H5 as [init' [fl' [ml' H5]]].
    exists init', fl', ml'. rewrite indexr_skip; auto.
Qed. 

Lemma wf_field_hit: forall {f fl ct Tf}, wf_field_decl fl ct -> indexr f fl = Some Tf ->
  wf_ty Tf ct.
Proof.
  intros. induction H. inversion H0. destruct (f =? length tail) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H0. inversion H0; subst.
    inversion H; auto.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H0; auto.
Qed.

Lemma wf_ct_to_Tf: forall {c ct init fl ml f Tf}, wf_ct ct -> indexr c ct = Some (cls_def fl init ml) ->
  indexr f fl = Some Tf ->
  wf_ty Tf ct.
Proof.
  intros. induction H. inversion H0. destruct (c =? length ct) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H0; subst. inversion H0; subst.
    specialize (wf_field_hit H3 H1) as H4. inversion H4; subst. specialize (indexr_var_some' H5) as H5'.
    econstructor; eauto. erewrite indexr_skip; eauto. lia. all: econstructor; eauto.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H0; auto. intuition.
    inversion H4; subst. econstructor; eauto. erewrite indexr_skip; eauto. apply indexr_var_some' in H5; lia.
    all: econstructor; eauto.
Qed.

Lemma wf_field_inequal: forall {f fl ct c ts}, wf_field_decl fl ct -> indexr f fl = Some (TCls c ts) ->
  ts <> TSUnique.
Proof.
  intros. induction H. inversion H0. destruct (f =? length tail) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H0. inversion H0; subst.
    specialize (H1 c ts0). intuition. subst. inversion H4.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H0; auto.
Qed.

Lemma wf_ct_to_Tf_ts: forall {c' ct init fl ml f c ts}, wf_ct ct -> indexr c ct = Some (cls_def fl init ml) ->
  indexr f fl = Some (TCls c' ts) ->
  ts <> TSUnique.
Proof.
  intros. induction H. inversion H0. destruct (c =? length ct) eqn: E1.
  + apply Nat.eqb_eq in E1; subst. rewrite indexr_head in H0. inversion H0; subst.
    specialize (wf_field_inequal H3 H1) as Heq. intuition.
  + apply Nat.eqb_neq in E1. rewrite indexr_skip in H0; auto.
Qed.

(* open and close *)
Definition open_var (k: nat)(u: var)(x: var) : var :=
  match x with 
  | varF i    =>   varF i
  | varB x    =>   if Nat.eqb k x then u else varB x
end
.  
#[global] Hint Unfold open_var : core.


(* opening an exmpression with an expression *)
Definition open_rec_tm (k: nat)(u: var)(t: tm) : tm :=
   match t with
   | ttrue            =>   ttrue
   | tfalse           =>   tfalse
   | tvar x           =>   tvar (open_var k u x)
   | tfacc x f        =>   tfacc (open_var k u x) f
   | toid  l          =>   toid l
   | toidfacc l f     =>   toidfacc l f
 (*  | tobj T fs        =>   tobj T fs *)
end
.
Definition open_tm u u' t := open_rec_tm 1 u' (open_rec_tm 0 u t).
Definition open_tm' {A : Type} (env : list A) t := open_rec_tm 1 $(S (length env)) (open_rec_tm 0 $(length env) t).

(* opening a statement with a variable *)
Fixpoint open_rec_stmt(k: nat)(u: var)(s:stmt) : stmt :=
    match s with 
    | sskip               =>   sskip
    | sassgn x1 x2        =>   sassgn (open_var k u x1) (open_var k u x2)
    | sload x y f         =>   sload (open_var k u x)(open_var k u y) f
    | sstore  x f y       =>   sstore (open_var k u x) f (open_var k u y)
    | smcall x y m p      =>   smcall (open_var k u x) (open_var k u y) m (open_var k u p)
    | slettm T e s        =>   slettm T (open_rec_tm k u e)(open_rec_stmt (S k) u s)
    | sletnew c c1 ps s    =>  sletnew c c1 ps (open_rec_stmt (S k) u s)
    | sif x s1 s2         =>   sif (open_var k u x)(open_rec_stmt k u s1)(open_rec_stmt k u s2)
    | sloop x c l s           =>   sloop (open_var k u x) c l (open_rec_stmt k u s)
    | sseq s1 s2          =>   sseq (open_rec_stmt k u s1)(open_rec_stmt k u s2)
end
.
Definition open_stmt u u' s := (open_rec_stmt 1 u' (open_rec_stmt 0 u s)).
Definition open_stmt' {A : Type} (env : list A) s := open_rec_stmt 1 $(S (length env)) (open_rec_stmt 0 $(length env) s).

Module OpeningNotations.
  Declare Scope opening.
  Notation "[[ k ~> u ]]ᵛ x"  := (open_var k u x) (at level 10) : opening.
  Notation "[[ k ~> u ]]ᵗ t"  := (open_rec_tm k u t) (at level 10) : opening.
  Notation "[[ k ~> u ]]ˢ s"  := (open_rec_stmt k u s) (at level 10) : opening.
  Notation "t  <~ᵗ u ; u'"    := (open_tm u u' t) (at level 10, u at next level) : opening.
  Notation "s  <~ˢ u ; u'"    := (open_stmt u u' s) (at level 10, u at next level) : opening.
End OpeningNotations.
Import OpeningNotations.
Local Open Scope opening.

Inductive closed_var: nat(*B*) -> nat(*F*) -> var -> Prop :=
| cl_varb : forall b f x,
    x < b ->
    closed_var b f (varB x)
| cl_varf : forall b f x,
    x < f ->
    closed_var b f (varF x)
.
#[global] Hint Constructors closed_var : core.

Inductive closed_var_list: nat(*B*) -> nat(*F*) -> list var -> Prop := 
| cl_varlst_nil : forall b f,
   closed_var_list b f []
| cl_varlst_cons : forall b f x xs,
   closed_var b f x ->
   closed_var_list b f xs ->
   closed_var_list b f (x::xs)
.

Lemma cl_var_ls_inversion: forall x xs b f, closed_var_list b f (x::xs) -> closed_var_list b f xs.
Proof. intros. inversion H. subst. auto.
Qed. 

Inductive closed_tm: nat (*B*) -> nat (*F*) -> tm -> Prop :=
  | cl_tture: forall b f,
      closed_tm b f ttrue
  | cl_tfalse: forall b f,
      closed_tm b f tfalse
  | cl_tvar: forall b f x,
      closed_var b f x ->
      closed_tm b f (tvar x)
  | cl_tfacc: forall b f x fd,
      closed_var b f x ->
      closed_tm b f (tfacc x fd)
  | closed_toid: forall b f l,
      closed_tm b f (toid l)
  | closed_tobj: forall b f l fd,
      closed_tm b f (toidfacc l fd)  
.
#[global] Hint Constructors closed_tm : core.

Inductive closed_stmt: nat (*B*) -> nat (*F*) -> stmt -> Prop :=
  | cl_sskip: forall b f,
      closed_stmt b f sskip
  | cl_assign: forall b f x y,
      closed_var b f x ->
      closed_var b f y ->
      closed_stmt b f (sassgn x y)
  | cl_sload: forall b f x y fd,
      closed_var b f x ->
      closed_var b f y ->
      closed_stmt b f (sload x y fd)
  | cl_store: forall b f x y fd,
      closed_var b f x ->
      closed_var b f y ->
      closed_stmt b f (sstore x fd y)
  | cl_smcall: forall b f x y m p,
      closed_var b f x ->
      closed_var b f y ->
      closed_var b f p ->
      closed_stmt b f (smcall x y m p)
  | cl_slettm: forall b f t s T,
      closed_tm b f t ->
      closed_stmt (S b) f s ->
      closed_stmt b f (slettm T t s)
  | cl_sletnew: forall b f c1 c2  ps s,
      closed_var_list b f ps ->
      closed_stmt (S b) f s ->
      closed_stmt b f (sletnew c1 c2 ps s)
  | cl_sif: forall b f x s1 s2,
      closed_var b f x ->
      closed_stmt b f s1 ->
      closed_stmt b f s2 ->
      closed_stmt b f (sif x s1 s2)
  | cl_slopp: forall b f x c l s,
      closed_var b f x ->
      closed_stmt b f s ->
      closed_stmt b f (sloop x c l s)
  | cl_sseq: forall b f s1 s2,
      closed_stmt b f s1 ->
      closed_stmt b f s2 ->
      closed_stmt b f (sseq s1 s2)
  .
#[global] Hint Constructors closed_stmt : core.

Lemma closed_var_open_id : forall {x b f}, closed_var b f x -> forall {n}, b <= n -> 
  forall {y}, [[n ~> y ]]ᵛ  x =  x.
Proof. intros t b f H. inversion H; subst; intros; simpl; auto.
  destruct (Nat.eqb n x) eqn:Heq; auto. apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma closed_tm_open_id : forall {t b f}, closed_tm b f t -> forall {n}, b <= n -> 
  forall {x}, [[n ~> x ]]ᵗ t = t.
Proof. intros t b f H. inversion H; subst; intros; simpl; auto.
  all: erewrite closed_var_open_id; eauto.
Qed.

Lemma closed_stmt_open_id : forall {t b f}, closed_stmt b f t -> forall {n}, b <= n -> 
  forall {x}, [[n ~> x ]]ˢ t = t.
Proof. intros s b f H. induction H; subst; intros; simpl; auto.
  all: try erewrite closed_tm_open_id; eauto.
  all: repeat try erewrite closed_var_open_id; eauto.
  all: try erewrite IHclosed_stmt; eauto. 
  all: try lia.
  erewrite IHclosed_stmt1. erewrite IHclosed_stmt2; eauto. lia.
  erewrite IHclosed_stmt1. erewrite IHclosed_stmt2; eauto. lia.
Qed.

Lemma closed_var_monotone:  forall {x b f}, closed_var b f x -> 
  forall {b' f' }, b <= b' -> f <= f' -> closed_var b' f' x.
Proof. intros x b f H. induction H; intuition; try solve[inversion H; subst; intuition].
Qed.

Lemma closed_varlist_monotone: forall {xs b f}, closed_var_list b f xs -> 
  forall {b' f' }, b <= b' -> f <= f' -> closed_var_list b' f' xs.
Proof. intros xs b f H. induction H; intuition; try solve[inversion H; subst; intuition].
  all: try econstructor; try eapply closed_var_monotone; eauto.
Qed.

Lemma closed_tm_monotone:  forall {t b f}, closed_tm b f t -> 
  forall {b' f' }, b <= b' -> f <= f' -> closed_tm b' f' t.
Proof.
  intros t b f H. induction H; intuition; try solve[inversion H; subst; intuition].
Qed.

Lemma closed_stmt_monotone:  forall {s b f}, closed_stmt b f s -> 
  forall {b' f' }, b <= b' -> f <= f' -> closed_stmt b' f' s.
Proof.
  intros s b f H. induction H; intuition; try solve[inversion H; subst; intuition].
  all: try econstructor; try eapply closed_var_monotone; try eapply closed_varlist_monotone;
  try eapply closed_tm_monotone; eauto. all: specialize (IHclosed_stmt (S b') f');
  assert (S b <= S b') by lia; auto.
Qed.

Lemma closed_var_open : forall {y b f}, closed_var (S b) f y -> 
  forall {x}, x < f -> closed_var b f ([[ b ~> $x ]]ᵛ y).
  intros. inversion H; subst; simpl; auto. destruct (Nat.eqb b x0) eqn:Heq; intuition.
  apply Nat.eqb_neq in Heq. constructor. lia.
Qed.

Lemma closed_var_open' : forall {x b f}, closed_var (S b) f x -> forall {y}, y <= f -> forall {z}, closed_var 0 y z -> closed_var b f ([[ b ~> z ]]ᵛ x).
Proof.  intros. inversion H; inversion H1; subst; simpl; intuition.
  destruct (Nat.eqb b x0) eqn:Heq; intuition. apply Nat.eqb_neq in Heq. constructor. lia.
Qed.

(* substitutions *)

Definition subst_var (v: var)(y u: nat) : var :=
  match v with 
  | varF x => varF (if Nat.eqb x y then u else (pred x))
  | varB x => varB x
end.

Definition subst_tm (t: tm)(v u: nat) : tm :=
  match t with 
  | ttrue     =>  ttrue
  | tfalse    =>  tfalse
  | tvar x    =>  tvar (subst_var x v u)
  | tfacc x f =>  tfacc (subst_var x v u) f
  | toid l    =>  toid l
  | tnull     =>  tnull
end.

Fixpoint subst_stmt(s: stmt)(v u : nat) : stmt :=
  match s with 
  | sskip              =>  sskip
  | sassgn x y         =>  sassgn (subst_var x v u)(subst_var y v u)
  | sload x y f        =>  sload (subst_var x v u)(subst_var y v u) f 
  | sstore x f y       =>  sstore (subst_var x v u) f (subst_var y v u)
  | smcall x y m z     =>  smcall (subst_var x v u)(subst_var y v u) m (subst_var z v u)
  | slettm T t s       =>  slettm T (subst_tm t v u)(subst_stmt s v u)
  | sletnew T1 T2 ps s    =>  sletnew T1 T2 (map (fun p => (subst_var p v u)) ps) (subst_stmt s v u)
  | sif x s1 s2        =>  sif (subst_var x v u)(subst_stmt s1 v u)(subst_stmt s2 v u)
  | sloop x c l s          =>  sloop (subst_var x v u) c l (subst_stmt s v u)
  | sseq s1 s2         =>  sseq (subst_stmt s1 v u)(subst_stmt s2 v u) 
end.


Module SubstitutionNotations.
  Declare Scope substitutions.
  Notation "{ v |-> y }ᵛ x"  := (subst_var x v y) (at level 10) : substitutions.
  Notation "{ v |-> t1 }ᵗ t" := (subst_tm t v t1) (at level 10) : substitutions.
  Notation "{ v |-> s1 }ˢ s" := (subst_stmt s v s1) (at level 10) : substitutions.
End SubstitutionNotations.
Import SubstitutionNotations.
Local Open Scope substitutions.

Lemma subst_var_id: forall {x b}, closed_var b 0 x -> forall {y},  {0 |-> y }ᵛ x = x.
Proof. intros. inversion H; subst; simpl; intuition.
Qed.


Lemma subst_tm_id : forall {t b }, closed_tm b 0 t -> forall {t1}, { 0 |-> t1 }ᵗ t = t.
Proof. induction t; intros b Hc; inversion Hc; subst; intros; simpl; intuition;
                       try solve [erewrite IHt; eauto];
                       try solve [erewrite IHt1; eauto; erewrite IHt2; eauto]; f_equal.
  all : eapply subst_var_id; eauto.
Qed.

Lemma subst_stmt_id: forall{s b}, closed_stmt b 0 s -> forall {s1}, { 0 |-> s1 }ˢ s = s.
Proof. induction s; intros b Hc; inversion Hc; subst; intros; simpl; intuition;
       repeat erewrite subst_var_id; eauto;
       repeat erewrite subst_tm_id; eauto;
       try solve [erewrite IHs; eauto];
       try solve [erewrite IHs1; eauto; erewrite IHs2; eauto].
       induction l.
       - simpl. erewrite IHs; eauto. 
       - simpl. assert (closed_stmt b 0 (sletnew t t0 l s)). 
            { apply cl_sletnew; auto. eapply cl_var_ls_inversion in H3. auto. }
         intuition. erewrite IHs; eauto. 
         inversion H3. subst. erewrite subst_var_id; eauto.
         apply H0 in H8. inversion H8. rewrite -> H2. rewrite -> H2. reflexivity.
Qed.

(* Definition consume (t: tm) () *)
