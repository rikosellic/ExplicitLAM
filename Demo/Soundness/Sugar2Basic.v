Require Import FV.Demo.Basic.BasicLambda.
Require Import FV.Demo.Sugar.SugarProp.
Require Import FV.utils.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Module B:= DemoBasic.
Module S:= DemoSugar.

Section Sugar2Basic.
Import Notations S.
(* Import Notations B. *)

Tactic Notation "baeq" := B.baeq.

Fixpoint tS2B (t:S.term): B.term:=
  match t with
  |  [[∅]]%s => B.empty_set
  |  S.var x => B.var x
  |  [[{t}]]%s => B.singleton (tS2B t) 
  |  [[ t1 ∩ t2]]%s => B.intersection (tS2B t1) (tS2B t2)
  |  [[ t1 ∪ t2]]%s => B.union (tS2B t1) (tS2B t2)
  end.
  
Fixpoint nS2B (p:S.prop): B.prop:=
  match p with
  | [[t1=t2]]%s => B.PEq (tS2B t1) (tS2B t2)
  | [[t1∈t2]]%s => B.PRel (tS2B t1) (tS2B t2)
  | S.PFalse =>B.PFalse
  | S.PTrue => B.PTrue
  | [[¬P]]%s=> B.PNot (nS2B P) 
  | [[P1 /\ P2]]%s=> B.PAnd  (nS2B P1) (nS2B P2) 
  | [[P1 \/ P2]]%s => B.POr  (nS2B P1) (nS2B P2) 
  | [[P1 -> P2]]%s=> B.PImpl  (nS2B P1) (nS2B P2) 
  | [[P1 <-> P2]]%s => B.PIff  (nS2B P1) (nS2B P2) 
  | S.PForall x P => B.PForall x (nS2B P)
  | S.PExists x P => B.PExists x (nS2B P)
  | _ => B.PFalse
end.

Fixpoint taskS2B (st:S.subst_task): B.subst_task:=
  match st with
  | nil => nil
  | (S.svar x t)::st' => (x, (tS2B t))::(taskS2B st')
  | _:: st' => taskS2B st'
end.

Definition S2B(P:S.prop): B.prop:= nS2B (S.preddef_elim P).

Lemma tS2B_same_lambda: forall t,
  S.term2tm t = B.term2tm (tS2B t).
Proof. induction t; try reflexivity; simpl; congruence. Qed.

Lemma naive_nS2B_same_lambda: forall P,
  naive P ->
  S.prop2tm P = B.prop2tm (nS2B P).
Proof.
  intros. 
  induction P; intros; simpl; try inversion H; subst; try rewrite <- IHP; try rewrite <- IHP1; try rewrite <- IHP2; try congruence.
  + now repeat rewrite <- tS2B_same_lambda.
  + now repeat rewrite <- tS2B_same_lambda.
Qed.

Lemma naive_S2B_same_lambda: forall P,
  naive P ->
  S.prop2tm P = B.prop2tm (S2B P).
Proof. 
  intros. unfold S2B. rewrite S.atom_naive_preddef_elim. 
  now apply naive_nS2B_same_lambda. now apply S.naive_is_atom_naive. 
Qed.

Lemma naive_sugar_aeq_S2B_aeq: forall p q,
  naive p ->
  naive q ->
  S.aeq p q <-> B.aeq (S2B p) (S2B q).
Proof. intros. rewrite S.aeq_FOL_LAM. rewrite B.aeq_FOL_LAM. now repeat rewrite <- naive_S2B_same_lambda. Qed.

Lemma naive_sugar_aeq_nS2B_aeq: forall p q,
  naive p ->
  naive q ->
  S.aeq p q <-> B.aeq (nS2B p) (nS2B q).
Proof. 
      intros. rewrite naive_sugar_aeq_S2B_aeq; try easy. unfold S2B. 
      repeat rewrite atom_naive_preddef_elim. 
      easy. now apply naive_is_atom_naive.
      now apply naive_is_atom_naive.
Qed.

Lemma tS2B_sub: forall t st,
  tS2B (S.term_sub st t) = B.term_sub (taskS2B st) (tS2B t).
Proof.
  induction t; intros; simpl; try rewrite <- IHt; try rewrite <- IHt1; try rewrite<- IHt2; try easy.
  induction st.
  + easy.
  + destruct a; simpl; try easy. S.destruct_name.
Qed. 

Lemma tS2B_occur: forall x t,
  S.term_occur x t = B.term_occur x (tS2B t).
Proof. intros. S.FOL2LAM. B.FOL2LAM. now rewrite tS2B_same_lambda. Qed.
 
Lemma S2B_task_term_occur: forall x st,
  Forall only_var_sub st ->
  S.task_term_occur x st = B.task_term_occur x (taskS2B st).
Proof.
  induction st; intros.
  + easy.
  + forall_cons H. destruct a; inversion H; subst.
      simpl. rewrite <- tS2B_occur. now rewrite IHst.
Qed.

Lemma S2B_free_occur: forall v P,
  naive P ->
  B.free_occur v (S2B P) = S.free_occur v P.
Proof.
  intros.  S.FOL2LAM. B.FOL2LAM. 
  now rewrite <- naive_S2B_same_lambda.
Qed.

Lemma nS2B_free_occur: forall v P,
  naive P ->
  B.free_occur v (nS2B P) = S.free_occur v P.
Proof.
  intros.  S.FOL2LAM. B.FOL2LAM.
  now rewrite <- naive_nS2B_same_lambda.
Qed.

Lemma S2B_reducev: forall x st,
  Forall only_var_sub st ->
  taskS2B (S.reducev x st) = B.reduce x (taskS2B st).
Proof.
  induction st; intros. easy.
  forall_cons H. destruct a; inversion H; subst.
  simpl. S.destruct_name. simpl. now rewrite IHst.
Qed.

Lemma term_ustr_tm_var: forall t,
  map uvar (B.tm_var (tS2B t)) = S.term_ustr t.
Proof. intros. induction t; simpl; try rewrite map_app; congruence. Qed.

Lemma nS2B_prop_ustr_prop_var: forall p,
  naive p ->
  map uvar (B.prop_var (nS2B p)) = S.prop_ustr p.
Proof. intros. induction H; simpl; try rewrite map_app; try repeat rewrite term_ustr_tm_var; congruence. Qed.

Lemma task_ustr_task_var: forall st,
  Forall only_var_sub st ->
  map uvar (B.task_var (taskS2B st)) = S.task_ustr st.
Proof.
  induction st; intros. easy. forall_cons H.
  destruct a; inversion H; subst.
  simpl. rewrite map_app. rewrite  term_ustr_tm_var. now rewrite IHst.
Qed.

Lemma nS2B_prop_sub: forall p st,
  Forall S.only_var_sub st ->
  naive p ->
  nS2B (S.prop_sub st p) = B.prop_sub (taskS2B st) (nS2B p).
Proof. 
  intros. rewrite <- prop_var_sub_prop_sub. 2: easy. 
  revert st H. induction H0; intros; simpl; try rewrite <- IHnaive;
  try rewrite <- IHnaive1; try rewrite <- IHnaive2; try easy;auto.
  + now repeat rewrite <- tS2B_sub.
  + now repeat rewrite <- tS2B_sub.
  + rewrite S2B_task_term_occur.  2: now apply reducev_Forall. rewrite S2B_reducev. 2: easy. 
      destruct (B.task_term_occur x (B.reduce x (taskS2B st))).
      - simpl. rewrite <- S2B_reducev. rewrite IHnaive. easy. now apply S.reducev_Forall. easy.
      - simpl. rewrite <-S2B_reducev. 2: easy.
        rewrite S.newv_list_new_name. simpl. repeat rewrite map_app.
        repeat rewrite nS2B_prop_ustr_prop_var. 2: easy.
        repeat rewrite task_ustr_task_var. 2: now apply reducev_Forall.
        rewrite IHnaive. easy. apply Forall_cons. easy. now apply reducev_Forall.
    + rewrite S2B_task_term_occur.  2: now apply reducev_Forall. rewrite S2B_reducev. 2: easy. 
      destruct (B.task_term_occur x (B.reduce x (taskS2B st))).
      - simpl. rewrite <- S2B_reducev. rewrite IHnaive. easy. now apply S.reducev_Forall. easy.
      - simpl. rewrite <-S2B_reducev. 2: easy.
        rewrite S.newv_list_new_name. simpl. repeat rewrite map_app.
        repeat rewrite nS2B_prop_ustr_prop_var. 2: easy.
        repeat rewrite task_ustr_task_var. 2: now apply reducev_Forall.
        rewrite IHnaive. easy. apply Forall_cons. easy. now apply reducev_Forall.
Qed.

Corollary S2B_prop_sub: forall p st,
  Forall S.only_var_sub st ->
  naive p ->
  S2B (S.prop_sub st p) = B.prop_sub (taskS2B st) (S2B p).
Proof.
  intros. unfold S2B. repeat rewrite atom_naive_preddef_elim; try now apply naive_is_atom_naive.
  now apply nS2B_prop_sub.
  rewrite <- prop_var_sub_prop_sub.
  apply prop_var_sub_keep_atom_naive. 
  now apply naive_is_atom_naive.
  easy.
Qed.

Ltac simpl_S2B:=
  repeat match goal with
  | H: context [S2B _ ]  |- _=> unfold S2B in H; simpl_preddef_elim_in H; simpl nS2B in H
  | |- context [S2B _ ] => unfold S2B; S.simpl_preddef_elim; simpl nS2B
  | |- _=> tauto
  end. 
  
Lemma S2B_sound: forall p,
  S.provable p ->
  B.provable (S2B p).
Proof.
  intros. induction H; intros. 
  + pose proof B.PForall_elim vr (tS2B t)(S2B P).
      eapply B.Alpha_congruence. 2: apply H0.
      etransitivity. 2: eapply naive_sugar_aeq_nS2B_aeq.
      4:{ simpl_preddef_elim. eapply S.aeq_PImpl. reflexivity.
           now apply subst_var_preddef_elim_aeq. }
      - simpl. unfold S2B in *. baeq. rewrite nS2B_prop_sub. simpl. baeq.
         repeat constructor. cgood. 
      - repeat constructor. cgood. cgood. apply prop_var_sub_keep_naive_iff. cgood.
      - cgood.
  + pose proof B.PExists_intros vr (tS2B t) (S2B P).
      eapply B.Alpha_congruence. 2: apply H0.
      etransitivity. 2: eapply naive_sugar_aeq_nS2B_aeq.
      4:{ simpl_preddef_elim. eapply S.aeq_PImpl. now apply subst_var_preddef_elim_aeq.
           reflexivity. }
      - simpl. unfold S2B in *. baeq. rewrite nS2B_prop_sub. simpl. baeq.
        repeat constructor. cgood.
      - cgood. repeat constructor. apply prop_var_sub_keep_naive_iff. cgood. cgood.
      - cgood.
  + pose proof B.PForall_intros vr (S2B P) (S2B Q).
      simpl_S2B. constructor. 
      - rewrite nS2B_free_occur. apply legal_preddef_elim_keep_no_free_occur. cgood. easy. cgood.
      - easy.
  + pose proof B.PExists_elim vr (S2B P) (S2B Q).
      simpl_S2B. constructor.
      - rewrite nS2B_free_occur. apply legal_preddef_elim_keep_no_free_occur. cgood. easy. cgood.
      - easy.
  + simpl_S2B. now constructor.
  + econstructor. simpl_S2B. eauto.
  + eapply B.PAnd_elim2. simpl_S2B. eauto.
  + simpl_S2B. now constructor.
  + simpl_S2B. now apply B.POr_intros2.
  + simpl_S2B. now constructor.
  + simpl_S2B. eapply B.PNot_EM. apply IHprovable1. easy.
  + simpl_S2B. eapply B.PNot_Contra. apply IHprovable1. easy.
  + simpl_S2B. constructor.
  + simpl_S2B. eapply B.Modus_Ponens; eauto.
  + simpl_S2B. constructor.
  + simpl_S2B. constructor.
  + simpl_S2B. now constructor.
  + simpl_S2B. now constructor.
  + simpl_S2B. now constructor.
  + simpl_S2B. constructor.
  + pose proof B.PEq_sub  (S2B P) x (tS2B t) (tS2B t').
      simpl_S2B. eapply B.Alpha_congruence.
      2:apply H0. baeq.
      - pose proof nS2B_prop_sub (preddef_elim P) [(svar x t)]. simpl in H1. rewrite <- H1.
        * apply naive_sugar_aeq_nS2B_aeq. cgood. apply prop_var_sub_keep_naive_iff.
           cgood. cgood. saeq.
        * repeat constructor.
        * cgood.
      - pose proof nS2B_prop_sub (preddef_elim P) [(svar x t')]. simpl in H1. rewrite <- H1.
        * apply naive_sugar_aeq_nS2B_aeq. cgood. apply prop_var_sub_keep_naive_iff.
           cgood. cgood. saeq.
        * repeat constructor.
        * cgood.
   + unfold S2B in *. eapply B.Alpha_congruence.
       2: apply IHprovable.
       apply naive_sugar_aeq_nS2B_aeq. 
       - cgood. apply preddef_unfold_keep_closed. easy. apply preddef_unfold_keep_pred_legal. easy.
       - cgood.
       - symmetry. now apply S.preddef_unfold_preddef_elim_aeq. 
   + unfold S2B in *. eapply B.Alpha_congruence.
       2: apply IHprovable.    
       apply naive_sugar_aeq_nS2B_aeq. 
       - cgood.
       - cgood. apply preddef_unfold_keep_closed. easy. apply preddef_unfold_keep_pred_legal. easy.
       - now apply S.preddef_unfold_preddef_elim_aeq. 
   + pose proof B.Empty. now cbv. 
   + apply B.Union. 
   + apply B.Intersection_iff. 
   + apply B.Singleton.
   + apply B.Extensionality.
   + apply B.Pairing.
   + pose proof B.Separation (S2B P).
       simpl_S2B. apply H2; rewrite nS2B_free_occur; try easy; try apply legal_preddef_elim_keep_no_free_occur; cgood. 
   + apply B.Union_iff.
   + apply B.PowerSet.
   + apply B.Infinity.
   + pose proof B.Replacement (S2B P). simpl_S2B.
       eapply B.Alpha_congruence.
       2: apply H2.
       - baeq. pose proof nS2B_prop_sub (preddef_elim P) [(svar _y _z)].
         simpl in H3. rewrite <- H3. apply naive_sugar_aeq_nS2B_aeq.
         cgood. apply prop_var_sub_keep_naive_iff. cgood. cgood.
         saeq. repeat constructor. cgood.
       - rewrite nS2B_free_occur. apply legal_preddef_elim_keep_no_free_occur. cgood. easy. cgood.
       - rewrite nS2B_free_occur. apply legal_preddef_elim_keep_no_free_occur. cgood. easy. cgood.
   (*** Axiom of Choice: Unfolding preddef in sugar is alpha equivalent with the rule in basic. ***)
   + pose proof B.Choice. eapply B.Alpha_congruence. 2: apply H.
       rewrite B.aeq_aeqb. reflexivity.
   + apply B.Regularity.
   + eapply B.Alpha_congruence. 2: apply IHprovable.
       apply naive_sugar_aeq_nS2B_aeq.
       - cgood.
       - cgood.
       - now apply S.preddef_elim_aeq. 
Qed.

End Sugar2Basic.
