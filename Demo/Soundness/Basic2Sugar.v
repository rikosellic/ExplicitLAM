Require Import FV.Demo.Basic.BasicLambda.
Require Import FV.Demo.Sugar.SugarProp.
Require Import FV.utils.
Require Import Coq.Lists.List.

Module B:=DemoBasic.
Module S:=DemoSugar.


Section Basic2Sugar.

Import Notations B.
(*Import Notations S.*)

Fixpoint B2S_term (t: B.term): S.term:=
  match t with
  |  B.empty_set => S.empty_set
  |  B.var x => S.var x
  |  B.singleton t => S.singleton (B2S_term t) 
  |  B.intersection t1 t2 => S.intersection (B2S_term t1) (B2S_term t2)
  |  B.union t1 t2 => S.union (B2S_term t1) (B2S_term t2)
  end.
  
Fixpoint B2S (p:B.prop): S.prop:=
  match p with
  | [[t1=t2]]%b => S.PEq (B2S_term t1) (B2S_term t2)
  | [[t1∈t2]]%b => S.PRel (B2S_term t1) (B2S_term t2)
  | B.PFalse => S.PFalse
  | B.PTrue => S.PTrue
  | [[¬P]]%b=> S.PNot (B2S P)
  | [[P1 /\ P2]]%b=> S.PAnd (B2S P1) (B2S P2)
  | [[P1 \/ P2]]%b => S.POr (B2S P1) (B2S P2)
  | [[P1 -> P2]]%b=> S.PImpl (B2S P1) (B2S P2)
  | [[P1 <-> P2]]%b => S.PIff (B2S P1) (B2S P2)
  | B.PForall x P => S.PForall x (B2S P)
  | B.PExists x P => S.PExists x (B2S P)
end.

Fixpoint B2S_subst_task (st:B.subst_task): S.subst_task:=
  match st with
  | nil => nil
  | (x,t)::st' => (S.svar x (B2S_term t))::(B2S_subst_task st')
end.

Lemma B2S_term_sub: forall t st,
  B2S_term (B.term_sub st t) = S.term_sub (B2S_subst_task st) (B2S_term t).
Proof.
  induction t; intros.
  + induction st. easy. destruct a. simpl. now destruct (V.eq_dec v t).
  + easy.
  + simpl. f_equal. auto.
  + simpl. f_equal; auto.
  + simpl. f_equal; auto.
Qed. 

Lemma B2S_term_same_lambda: forall t,
  B.term2tm t = S.term2tm (B2S_term t).
Proof. induction t; try reflexivity; simpl; congruence. Qed.

Lemma B2S_same_lambda: forall p,
  B.prop2tm p = S.prop2tm (B2S p).
Proof. induction p; try reflexivity; simpl; try repeat rewrite B2S_term_same_lambda; congruence. Qed.

Lemma B2S_subst_task_same_lambda: forall st,
  B.st_FOL2LAM st = S.st_FOL2LAM (B2S_subst_task st).
Proof.
  induction st.
  + easy.
  + destruct a. simpl. rewrite <- B2S_term_same_lambda. congruence.
Qed. 

Lemma B2S_task_term_occur: forall x st,
  B.task_term_occur x (reduce x st) = S.task_term_occur x (S.reducev x (B2S_subst_task st)).
Proof.
  intros. B.FOL2LAM. S.FOL2LAM. now rewrite <- B2S_subst_task_same_lambda.
Qed.   

Lemma B2S_reduce: forall x st,
  B2S_subst_task (reduce x st) = S.reducev x (B2S_subst_task st).
Proof.
  induction st.
  + easy.
  + destruct a. simpl. destruct (V.eq_dec x t). easy. simpl. congruence.
Qed.

Lemma tm_var_term_ustr: forall t,
  map uvar (B.tm_var t)  = S.term_ustr (B2S_term t).
Proof. intros. induction t; simpl; try rewrite map_app; congruence. Qed.
  
Lemma prop_var_prop_ustr: forall p,
  map uvar (B.prop_var p) = S.prop_ustr (B2S p).
Proof. intros;induction p; simpl; try rewrite map_app;try repeat rewrite tm_var_term_ustr; congruence. Qed.

Lemma task_var_task_ustr: forall st,
  map uvar (B.task_var st) = S.task_ustr (B2S_subst_task st).
Proof. 
  induction st. easy.
  destruct a. simpl. rewrite map_app. rewrite tm_var_term_ustr. congruence. 
Qed.

Lemma B2S_prop_sub_prop_var_sub: forall p st,
  B2S (B.prop_sub st p) = S.prop_var_sub (B2S_subst_task st) (B2S p).
Proof.
  induction p; intros; try easy; simpl; try repeat rewrite B2S_term_sub; try congruence.
  + rewrite <- B2S_task_term_occur. 
      destruct (B.task_term_occur x (reduce x st)).
      - simpl. f_equal. rewrite IHp. now rewrite B2S_reduce. 
      - simpl. rewrite <- B2S_reduce.  rewrite S.newv_list_new_name.
         repeat rewrite map_cons. repeat rewrite map_app.
         repeat rewrite prop_var_prop_ustr. repeat rewrite task_var_task_ustr. 
         f_equal. apply IHp.  
  + rewrite <- B2S_task_term_occur. 
      destruct (B.task_term_occur x (reduce x st)).
      - simpl. f_equal. rewrite IHp. now rewrite B2S_reduce. 
      - simpl. rewrite <- B2S_reduce.  rewrite S.newv_list_new_name.
         repeat rewrite map_cons. repeat rewrite map_app.
         repeat rewrite prop_var_prop_ustr. repeat rewrite task_var_task_ustr. 
         f_equal. apply IHp. 
Qed.

Lemma B2S_subst_task_only_var_sub: forall st,
  Forall S.only_var_sub (B2S_subst_task st).
Proof.
  induction st.
  + constructor.
  + destruct a. apply Forall_cons. constructor. easy.
Qed.

Corollary B2S_prop_sub: forall p st,
  B2S (B.prop_sub st p) = S.prop_sub (B2S_subst_task st) (B2S p).
Proof.
  intros. rewrite B2S_prop_sub_prop_var_sub. rewrite S.prop_var_sub_prop_sub. easy.
  apply B2S_subst_task_only_var_sub.
Qed.

Lemma basic_aeq_B2S_aeq: forall p q,
  B.aeq p q <-> S.aeq (B2S p) (B2S q).
Proof. intros. rewrite B.aeq_FOL_LAM. rewrite S.aeq_FOL_LAM. now repeat rewrite <- B2S_same_lambda. Qed.
  
Lemma B2S_free_occur: forall x p,
  B.free_occur x p = S.free_occur x (B2S p).
Proof.
  intros. B.FOL2LAM. S.FOL2LAM. rewrite <- B2S_same_lambda. easy.
Qed.

Lemma B2S_naive: forall P,
  S.naive (B2S P).
Proof. induction P; constructor; auto. Qed.

Corollary B2S_good: forall P,
  S.good (B2S P).
Proof. intros. apply S.naive_is_good. apply B2S_naive. Qed.
  
Theorem B2S_sound: forall p, B.provable p -> S.provable (B2S p).
Proof.
  intros.
  induction H; try now constructor; try apply B2S_good.
  + simpl. rewrite B2S_prop_sub. simpl. constructor. apply B2S_good.
  + simpl. rewrite B2S_prop_sub. simpl. constructor. apply B2S_good.
  + simpl. rewrite B2S_free_occur in H. simpl in IHprovable. constructor; try easy; apply B2S_good.  
  + simpl. rewrite B2S_free_occur in H. simpl in IHprovable. constructor; try easy; apply B2S_good.
  + econstructor. apply B2S_good. simpl in IHprovable. 2: apply IHprovable. apply B2S_good. 
  + apply S.PAnd_elim2 with (B2S P). apply B2S_good. apply B2S_good. easy. 
  + eapply S.PNot_EM. simpl in IHprovable1. simpl in IHprovable2. 3: apply IHprovable1. 
      apply B2S_good. apply B2S_good. easy.
  + eapply S.PNot_Contra. simpl in IHprovable1. simpl in IHprovable2.
      3: apply IHprovable1. apply B2S_good. apply B2S_good. easy.
  + eapply S.Modus_Ponens. simpl in IHprovable1. simpl in IHprovable2. 3: apply IHprovable1. 
      apply B2S_good. apply B2S_good. easy.
  + simpl. repeat rewrite B2S_prop_sub. simpl. apply S.PEq_sub. apply B2S_good.
  + pose proof S.Empty. eapply S.Alpha_congruence. 4: eapply S.preddef_elim_provable. 4: apply H. 
      - now rewrite S.good_goodb.
      - now rewrite S.good_goodb.
      - now rewrite S.aeq_aeqb. 
  + rewrite B2S_free_occur in H. rewrite B2S_free_occur in H0. simpl. constructor; try easy. now apply B2S_good.
  + pose proof S.PowerSet.  eapply S.Alpha_congruence. 4: eapply S.preddef_elim_provable. 4:eauto. 
      - now rewrite S.good_goodb.
      - now rewrite S.good_goodb.
      - now rewrite S.aeq_aeqb. 
  + pose proof S.Infinity.  eapply S.Alpha_congruence. 4: eapply S.preddef_elim_provable. 4:eauto. 
      - now rewrite S.good_goodb.
      - now rewrite S.good_goodb.
      - now rewrite S.aeq_aeqb. 
  + rewrite B2S_free_occur in H. rewrite B2S_free_occur in H0. simpl. 
      repeat rewrite B2S_prop_sub.  apply S.Replacement; try easy. apply B2S_good.
  + pose proof S.Choice.  eapply S.Alpha_congruence. 4: eapply S.preddef_elim_provable. 4:eauto. 
      - now rewrite S.good_goodb.
      - now rewrite S.good_goodb.
      - now rewrite S.aeq_aeqb. 
  + pose proof S.Regularity.  eapply S.Alpha_congruence. 4: eapply S.preddef_elim_provable. 4:eauto. 
      - now rewrite S.good_goodb.
      - now rewrite S.good_goodb.
      - now rewrite S.aeq_aeqb. 
  + eapply S.Alpha_congruence. 4: eauto.
     - apply B2S_good.
     - apply B2S_good.
     - now apply basic_aeq_B2S_aeq.
Qed.

End Basic2Sugar.
