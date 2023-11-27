Require Import Coq.Sorting.Permutation.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationClasses.
Require Import Operators_Properties.
Require Import Coq.Lists.List.
Require Import FV.Demo.Basic.Basic.
Require Import FV.utils.
Require Import FV.Demo.Lambda.
Import ListNotations.


Module DemoBasic.
Import LAM.
Include DemoBasicFOL.

Fixpoint term2tm (t:term):tm:=
 match t with
 | empty_set =>cons iempty
 | singleton x => app (cons isingleton) (term2tm x)
 | var x => LAM.var (uvar x)
 | intersection x y => app (cons iintersection) (app (term2tm x) (term2tm y))
 | union x y => app (cons iunion) (app (term2tm x) (term2tm y))
 end.
 
 Fixpoint prop2tm (d:prop):tm:=
  match d with
  | PEq t1 t2 => app (cons iPEq) (app (term2tm t1) (term2tm t2))
  | PRel t1 t2 => app (cons iPRel) (app (term2tm t1) (term2tm t2))
  | PFalse => cons iPFalse
  | PTrue => cons iPTrue
  | PNot P => app (cons iPNot) (prop2tm P)
  | PAnd P1 P2 => app (cons iPAnd) (app (prop2tm P1) (prop2tm P2))
  | POr P1 P2 => app (cons iPOr) (app (prop2tm P1) (prop2tm P2))
  | PImpl P1 P2 => app (cons iPImpl) (app (prop2tm P1) (prop2tm P2))
  | PIff P1 P2 => app (cons iPIff) (app (prop2tm P1) (prop2tm P2))
  | PForall x P => app (cons iPForall) (abs (uvar x) (prop2tm P))
  | PExists x P => app (cons iPExists) (abs (uvar x) (prop2tm P))
end.

Fixpoint tm2term (t:tm):option term:= 
  match t with
  | cons iempty => Some empty_set
  | LAM.var x => match x with
                  | uvar s => Some (var s)
                  | _ => None
                  end
  | app (cons isingleton) t0 =>  match tm2term t0 with
                                                 | Some m =>  Some (singleton m)
                                                 | None => None
                                                end
  | app (cons iintersection) (app t1 t2)=>  match tm2term t1, tm2term t2 with
                                                                  | Some m1, Some m2 => Some (intersection m1 m2)
                                                                  | _ , _ => None
                                                                end
  | app (cons iunion) (app t1 t2)=>  match tm2term t1, tm2term t2 with
                                                                  | Some m1, Some m2 => Some (union m1 m2)
                                                                  | _ , _ => None
                                                                end
  | _ => None
  end. 
  
Fixpoint tm2prop(t:tm): option prop:=
  match t with
  | cons iPTrue => Some PTrue
  | cons iPFalse => Some PFalse
  | app (cons iPEq) (app t1 t2) => match tm2term t1, tm2term t2 with
                                                   | Some m1, Some m2 => Some (PEq m1 m2)
                                                   | _ , _ => None
                                                  end
  | app (cons iPRel) (app t1 t2) => match tm2term t1, tm2term t2 with
                                                     | Some m1, Some m2 => Some (PRel m1 m2)
                                                     | _ , _ => None
                                                    end
  | app (cons iPNot) t0 => match tm2prop t0 with
                                        | Some d => Some (PNot d)
                                        | _ => None
                                        end
  | app (cons iPAnd) (app t1 t2) => match tm2prop t1, tm2prop t2 with
                                                        | Some d1, Some d2 => Some (PAnd d1 d2)
                                                        | _ , _ => None
                                                       end
  | app (cons iPOr) (app t1 t2) => match tm2prop t1, tm2prop t2 with
                                                        | Some d1, Some d2 => Some (POr d1 d2)
                                                        | _ , _ => None
                                                       end
  | app (cons iPImpl) (app t1 t2) => match tm2prop t1, tm2prop t2 with
                                                        | Some d1, Some d2 => Some (PImpl d1 d2)
                                                        | _ , _ => None
                                                       end
  | app (cons iPIff) (app t1 t2) => match tm2prop t1, tm2prop t2 with
                                                        | Some d1, Some d2 => Some (PIff d1 d2)
                                                        | _ , _ => None
                                                       end
  | app (cons iPForall) (abs x t0) => match x with
                                                       | uvar s =>  match tm2prop t0 with
                                                                           | Some d => Some (PForall s d)
                                                                           | _ => None
                                                                          end
                                                       |  _ => None
                                                       end
  | app (cons iPExists) (abs x t0) => match x with 
                                                       | uvar s => match tm2prop t0 with
                                                                         | Some d => Some (PExists s d)
                                                                         | _ => None
                                                                         end
                                                       | _ => None
                                                       end
  | _ => None
end. 


Definition st_FOL2LAM (st:subst_task):LAM.subst_task:=
  map (fun p => (uvar (fst p), term2tm (snd p))) st.

Local Ltac repeat_rewrite:=
  simpl; (repeat match goal with
  | [|- context [map _ (_++_)] ] => rewrite map_app 
  | [|- context [variable_list  (_++_)] ] => rewrite variable_list_app
  | [|- context [predname_list  (_++_)] ] => rewrite predname_list_app
  | [H: _ =  _  |- _] => rewrite H
  end); try easy.

Lemma term2tm_tm2term: forall (t:term),
  tm2term (term2tm t) = Some t.
Proof. induction t; repeat_rewrite. Qed.

Lemma prop2tm_tm2prop: forall (P:prop),
  tm2prop (prop2tm P) = Some P.
Proof. induction P; repeat_rewrite; rewrite 2 term2tm_tm2term; easy. Qed.

Lemma tm_var_FOL_LAM: forall t,
  map uvar (tm_var t) = LAM.tm_var (term2tm t).
Proof. induction t; repeat_rewrite. Qed.

Lemma tm_var_FOL_LAM2: forall t,
  tm_var t = variable_list (LAM.tm_var (term2tm t)).
Proof. induction t; repeat_rewrite. Qed.

Lemma prop_var_FOL_LAM: forall P,
  map uvar (prop_var P) = LAM.tm_var (prop2tm P).
Proof.  induction P; repeat_rewrite; try now rewrite 2 tm_var_FOL_LAM.  Qed.
  
Lemma prop_var_FOL_LAM2: forall P,
  prop_var P = variable_list (LAM.tm_var (prop2tm P)).
Proof.  induction P; repeat_rewrite; now rewrite 2 tm_var_FOL_LAM2.  Qed.

Lemma task_var_FOL_LAM: forall st,
  map uvar (task_var st) = LAM.task_var (st_FOL2LAM st).
Proof.
  induction st. easy.
  destruct a. simpl. rewrite map_app. rewrite IHst. rewrite tm_var_FOL_LAM. easy.
Qed.

Lemma task_var_FOL_LAM2: forall st,
  task_var st = variable_list (LAM.task_var (st_FOL2LAM st)).
Proof.
  induction st. easy.
  destruct a. simpl. rewrite variable_list_app. rewrite IHst. now rewrite tm_var_FOL_LAM2.
Qed.

Lemma term_occur_FOL_LAM: forall (x: V.t) t,
  term_occur x t = LAM.free_occur (uvar x) (term2tm t).
Proof. 
  induction t; repeat_rewrite. unfold LAM.var_occur. 
  destruct (var_eq_dec x v); destruct (V.eq_dec x v); congruence.
Qed.

Lemma free_occur_FOL_LAM: forall (x:V.t) P,
 free_occur x P = LAM.free_occur (uvar x) (prop2tm P).
Proof. 
  induction P; repeat_rewrite. 
  + now rewrite 2 term_occur_FOL_LAM.
  + now rewrite 2 term_occur_FOL_LAM.
  + destruct (V.eq_dec x x0); destruct (var_eq_dec x x0); congruence.
  + destruct (V.eq_dec x x0); destruct (var_eq_dec x x0); congruence.
Qed.

Lemma task_term_occur_FOL_LAM: forall (x:V.t) st,
 task_term_occur x st = LAM.st_tm_occur (uvar x) (st_FOL2LAM st).
Proof. induction st. easy.  simpl. rewrite IHst. destruct a. simpl. now rewrite term_occur_FOL_LAM. Qed.

Lemma reduce_FOL_LAM: forall x st,
  st_FOL2LAM (reduce x st) = LAM.reduce (uvar x) (st_FOL2LAM st).
Proof.
  induction st. easy.
  destruct a. simpl. destruct (V.eq_dec x t); destruct (var_eq_dec x t); try congruence.
  simpl. now rewrite IHst. 
Qed.

Local Ltac LAM2FOL_aux1:=
  repeat match goal with
  | [H: context [LAM.free_occur (uvar _) (prop2tm _)] |- _ ] => rewrite <- free_occur_FOL_LAM in H
  | [H: context [LAM.free_occur (uvar _) (term2tm _)] |- _ ] => rewrite <- term_occur_FOL_LAM in H
  | [H: context [LAM.st_tm_occur (uvar _ ) (st_FOL2LAM _)] |- _ ] => rewrite <- task_term_occur_FOL_LAM in H
  | [H: context [LAM.reduce (uvar _) (st_FOL2LAM _)] |- _ ] => rewrite <- reduce_FOL_LAM in H
  | [H: context [variable_list  (_++_)] |- _ ] => rewrite variable_list_app in H
  | [H: context [predname_list  (_++_)] |- _ ] => rewrite predname_list_app in H
  | [H: context [variable_list (LAM.tm_var (prop2tm _ ))] |- _ ] => rewrite <- prop_var_FOL_LAM2 in H
  | [H: context [variable_list (LAM.tm_var (term2tm _ ))] |- _ ] => rewrite <- tm_var_FOL_LAM2 in H
  | [H: context [variable_list (LAM.task_var (st_FOL2LAM _))] |- _ ] => rewrite <- task_var_FOL_LAM2 in H
  | [|- context [LAM.free_occur (uvar _) (prop2tm _)] ] => rewrite <- free_occur_FOL_LAM 
  | [|- context [LAM.free_occur (uvar _) (term2tm _)] ] => rewrite <- term_occur_FOL_LAM 
  | [|- context [LAM.st_tm_occur (uvar _ ) (st_FOL2LAM _)] ] => rewrite <- task_term_occur_FOL_LAM 
  | [|- context [LAM.reduce (uvar _) (st_FOL2LAM _)] ] => rewrite <- reduce_FOL_LAM
  | [|- context [variable_list  (_++_)] ] => rewrite variable_list_app 
  | [|- context [predname_list  (_++_)] ] => rewrite predname_list_app 
  | [|- context [variable_list (LAM.tm_var (prop2tm _ ))]  ] => rewrite <- prop_var_FOL_LAM2 
  | [|- context [variable_list (LAM.tm_var (term2tm _ ))]  ] => rewrite <- tm_var_FOL_LAM2 
  | [|- context [variable_list (LAM.task_var (st_FOL2LAM _))] ] => rewrite <- task_var_FOL_LAM2
  end.

Lemma term_sub_FOL_LAM: forall t st,
  term2tm (term_sub st t) = subst (st_FOL2LAM st) (term2tm t).
Proof.
  induction t; intros; simpl; try congruence.
  induction st.
    + easy.
    + destruct a. simpl. destruct (var_eq_dec v t); destruct (V.eq_dec v t);  congruence.
Qed.


Lemma prop_sub_FOL_LAM: forall P st,
  prop2tm (prop_sub st P) = subst (st_FOL2LAM st) (prop2tm P).
Proof.
  induction P; intros; simpl; try congruence.
  + rewrite 2 term_sub_FOL_LAM. easy.
  + rewrite 2 term_sub_FOL_LAM. easy.
  + LAM2FOL_aux1.
      destruct ( task_term_occur x (reduce x st)).
      - simpl. rewrite IHP. easy.
      - simpl. repeat f_equal. apply IHP.   
  + LAM2FOL_aux1.  
      destruct (task_term_occur x (reduce x st)).
      - simpl. rewrite IHP. easy. 
      - simpl. repeat f_equal. apply IHP.
Qed.

Definition binder_FOL2LAM(bd:binder_pair): LAM.binder_pair:=
  match bd with
  | (x,y,b) => (uvar x, uvar y,b)
  end.

Definition binder_list_FOL2LAM (bd:binder_list):LAM.binder_list:=
  map binder_FOL2LAM bd.
  
Lemma binder_FOL2LAM_injective: forall p1 p2,
  binder_FOL2LAM p1 = binder_FOL2LAM p2 -> p1 = p2.
Proof. intros. destruct p1 as [ [? ?] ? ]. destruct p2 as [ [? ?] ?]. injection H; intros. congruence. Qed.
  
Lemma binder_list_In_FOL_LAM: forall v1 v2 b bd,
  In (v1,v2,b) bd <-> In (uvar v1, uvar v2, b) (binder_list_FOL2LAM bd).
Proof.
  split; intros.
  + unfold binder_list_FOL2LAM. assert ((uvar v1, uvar v2, b) = binder_FOL2LAM (v1,v2,b)) by reflexivity. 
      rewrite H0. now apply in_map.
  + induction bd. inversion H. destruct H.
      left. now apply binder_FOL2LAM_injective.
      right. tauto.
Qed. 
       
Lemma binder_l_not_In_FOL_LAM: forall s bd,
  ~ In s (binder_l bd) <->  ~ In (uvar s) (LAM.binder_l (binder_list_FOL2LAM bd)).
Proof.
  split; intros.
  + induction bd. easy. destruct a as [ [? ?] ? ].
      simpl. simpl in H. apply deMorgan1 in H. destruct H. apply deMorgan2. split.
      congruence. tauto. 
  + induction bd. easy. destruct a as [ [? ?] ? ].
      simpl in H. apply deMorgan1 in H. simpl. destruct H. apply deMorgan2. split.
      congruence. tauto. 
Qed. 

Lemma update_FOL_LAM: forall x y bd,
  binder_list_FOL2LAM (update x y bd) = LAM.update (uvar x) (uvar y) (binder_list_FOL2LAM bd).
 Proof.
    induction bd. 
    + easy.
    + destruct a as [ [? ?] ?]. simpl. unfold str_occur. unfold var_occur. unfold LAM.var_occur.
        destruct (var_eq_dec x t); destruct (V.eq_dec x t); try congruence. 
        - simpl. rewrite IHbd. easy.
        - destruct (V.eq_dec y t0); destruct (var_eq_dec y t0); try congruence.
          simpl. rewrite IHbd. easy. simpl. rewrite IHbd. easy.
Qed.

Lemma binder_r_not_In_FOL_LAM: forall s bd,
  ~ In s (binder_r bd) <->  ~ In (uvar s) (LAM.binder_r (binder_list_FOL2LAM bd)).
Proof.
  split; intros.
  + induction bd. easy. destruct a as [ [? ?] ? ].
      simpl. simpl in H. apply deMorgan1 in H. destruct H. apply deMorgan2. split.
      congruence. tauto. 
  + induction bd. easy. destruct a as [ [? ?] ? ].
      simpl in H. apply deMorgan1 in H. simpl. destruct H. apply deMorgan2. split.
      congruence. tauto. 
Qed.

Lemma term_alpha_eq_FOL_LAM: forall bd t1 t2,
  term_alpha_eq bd t1 t2 <-> LAM.alpha_eq (binder_list_FOL2LAM bd) (term2tm t1) (term2tm t2).
Proof.
  split; intros.
  + induction H; simpl; try now repeat constructor.
      - apply str_aeq1. easy. now apply binder_list_In_FOL_LAM. 
      - apply str_aeq2; [now apply binder_l_not_In_FOL_LAM | now apply binder_r_not_In_FOL_LAM ].
  + revert t2 H. induction t1; intros; inversion H; subst. 
      - destruct t2; inversion H1; subst. apply binder_list_In_FOL_LAM in H4. now constructor.
      - destruct t2; inversion H1; subst. apply binder_l_not_In_FOL_LAM in H3.
        apply binder_r_not_In_FOL_LAM in H4. now constructor.
      - destruct t2; inversion H3; subst. now constructor.
      - inversion H4; subst. destruct t2; inversion H3; subst. constructor. now apply IHt1. 
      - inversion H4; subst. inversion H5; subst. destruct t2;inversion H3; subst.
        constructor. now apply IHt1_1. now apply IHt1_2.
      - inversion H4; subst. inversion H5; subst. destruct t2;inversion H3; subst.
        constructor. now apply IHt1_1. now apply IHt1_2.
Qed.
      
Lemma alpha_eq_FOL_LAM: forall bd P1 P2,
  alpha_eq bd P1 P2 <-> LAM.alpha_eq (binder_list_FOL2LAM bd) (prop2tm P1) (prop2tm P2).
Proof.
  split; intros.
  + induction H; simpl; try constructor;try constructor; try easy; try now apply term_alpha_eq_FOL_LAM.
     - rewrite <- update_FOL_LAM. apply IHalpha_eq.
     - rewrite <- update_FOL_LAM. apply IHalpha_eq.
  + revert bd P2 H. induction P1; intros; inversion H; subst.
      - inversion H4; subst. inversion H5; subst. destruct P2;inversion H3; subst. constructor; now apply term_alpha_eq_FOL_LAM.
      - inversion H4; subst. inversion H5; subst. destruct P2;inversion H3; subst. constructor; now apply term_alpha_eq_FOL_LAM.
      - destruct P2;inversion H3; subst. constructor.
      - destruct P2;inversion H3; subst. constructor.
      - inversion H4; subst. destruct P2; inversion H3; subst. constructor. now apply IHP1.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst.  constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst.  constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst.  constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst.  constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. constructor. 
        rewrite <- update_FOL_LAM in H8. specialize IHP1 with ((x,x0,true)::(update x x0 bd)) P2. simpl in IHP1. tauto.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. constructor.
        rewrite <- update_FOL_LAM in H8. specialize IHP1 with ((x,x0,true)::(update x x0 bd)) P2. simpl in IHP1. tauto.
Qed.

Corollary aeq_FOL_LAM: forall P1 P2,
  aeq P1 P2 <-> LAM.aeq (prop2tm P1) (prop2tm P2).
Proof.  apply alpha_eq_FOL_LAM with (bd:=nil). Qed.

Ltac LAM2FOL:=
  repeat match goal with
  | [H: LAM.alpha_eq (binder_list_FOL2LAM _) (term2tm _ ) (term2tm _) |- _ ] => rewrite <- term_alpha_eq_FOL_LAM in H
  | [H: LAM.alpha_eq (binder_list_FOL2LAM _) (prop2tm _ ) (prop2tm _) |-_ ]=> rewrite <- alpha_eq_FOL_LAM in H
  | [H: LAM.aeq (prop2tm _ ) (prop2tm _ ) |- _ ] => rewrite <- aeq_FOL_LAM in H
  | [H: context [LAM.update (uvar _ ) (uvar _ ) (binder_list_FOL2LAM _ )] |- _] => rewrite <- update_FOL_LAM in H
  | [H: ~ In (uvar _) (LAM.binder_l (binder_list_FOL2LAM _)) |- _ ] => rewrite <- binder_l_not_In_FOL_LAM in H
  | [H: ~ In (uvar _) (LAM.binder_r (binder_list_FOL2LAM _)) |- _ ] => rewrite <- binder_r_not_In_FOL_LAM in H
  | [H: In (uvar _ , uvar _ , true ) (binder_list_FOL2LAM _ ) |- _ ] => rewrite <- binder_list_In_FOL_LAM in H
  | [H: context [LAM.free_occur (uvar _) (prop2tm _)] |- _ ] => rewrite <- free_occur_FOL_LAM in H
  | [H: context [LAM.free_occur (uvar _) (term2tm _)] |- _ ] => rewrite <- term_occur_FOL_LAM in H
  | [H: context [LAM.st_tm_occur (uvar _ ) (st_FOL2LAM _)] |- _ ] => rewrite <- task_term_occur_FOL_LAM in H
  | [H: context [LAM.reduce (uvar _) (st_FOL2LAM _)] |- _ ] => rewrite <- reduce_FOL_LAM in H
  | [H: context [variable_list  (_++_)] |- _ ] => rewrite variable_list_app in H
  | [H: context [predname_list  (_++_)] |- _ ] => rewrite predname_list_app in H
  | [H: context [variable_list (LAM.tm_var (prop2tm _ ))] |- _ ] => rewrite <- prop_var_FOL_LAM2 in H
  | [H: context [variable_list (LAM.tm_var (term2tm _ ))] |- _ ] => rewrite <- tm_var_FOL_LAM2 in H
  | [H: context [variable_list (LAM.task_var (st_FOL2LAM _))] |- _ ] => rewrite <- task_var_FOL_LAM2 in H
  | [H: context [subst (st_FOL2LAM _) (term2tm _)] |- _ ] => rewrite <- term_sub_FOL_LAM in H
  | [H: context [subst (st_FOL2LAM _) (prop2tm _)] |- _ ] => rewrite <- prop_sub_FOL_LAM in H
  | [|- LAM.alpha_eq (binder_list_FOL2LAM _) (term2tm _ ) (term2tm _)  ] => rewrite <- term_alpha_eq_FOL_LAM 
  | [|-  LAM.alpha_eq (binder_list_FOL2LAM _) (prop2tm _ ) (prop2tm _) ]=> rewrite <- alpha_eq_FOL_LAM 
  | [|- LAM.aeq (prop2tm _ ) (prop2tm _) ] => rewrite <-aeq_FOL_LAM 
  | [|- context [LAM.update (uvar _ ) (uvar _ ) (binder_list_FOL2LAM _ )] ] => rewrite <- update_FOL_LAM 
  | [|- context [LAM.free_occur (uvar _) (prop2tm _)] ] => rewrite <- free_occur_FOL_LAM 
  | [|- context [LAM.free_occur (uvar _) (term2tm _)] ] => rewrite <- term_occur_FOL_LAM 
  | [|- context [LAM.st_tm_occur (uvar _ ) (st_FOL2LAM _)] ] => rewrite <- task_term_occur_FOL_LAM 
  | [|- context [LAM.reduce (uvar _) (st_FOL2LAM _)] ] => rewrite <- reduce_FOL_LAM
  | [|- context [variable_list  (_++_)] ] => rewrite variable_list_app 
  | [|- context [predname_list  (_++_)] ] => rewrite predname_list_app 
  | [|- context [variable_list (LAM.tm_var (prop2tm _ ))]  ] => rewrite <- prop_var_FOL_LAM2 
  | [|- context [variable_list (LAM.tm_var (term2tm _ ))]  ] => rewrite <- tm_var_FOL_LAM2 
  | [|- context [variable_list (LAM.task_var (st_FOL2LAM _))] ] => rewrite <- task_var_FOL_LAM2
  | [|- context [subst (st_FOL2LAM _) (term2tm _)]  ] => rewrite <- term_sub_FOL_LAM 
  | [|- context [subst (st_FOL2LAM _) (prop2tm _)]  ] => rewrite <- prop_sub_FOL_LAM 
  | [|- ~ In (uvar _) (LAM.binder_l (binder_list_FOL2LAM _))  ] => rewrite <- binder_l_not_In_FOL_LAM 
  | [|- ~ In (uvar _) (LAM.binder_r (binder_list_FOL2LAM _)) ] => rewrite <- binder_r_not_In_FOL_LAM 
  | [|- In (uvar _ , uvar _ , true ) (binder_list_FOL2LAM _ ) ] => rewrite <- binder_list_In_FOL_LAM
  end.

Ltac FOL2LAM:=
  repeat match goal with
  | [H: term_alpha_eq _ _ _ |- _ ] => rewrite term_alpha_eq_FOL_LAM in H
  | [H: alpha_eq _ _ _ |-_ ]=> rewrite alpha_eq_FOL_LAM in H
  | [H: aeq _ _ |- _ ] => rewrite aeq_FOL_LAM in H
  | [H: context [binder_list_FOL2LAM (update _ _ _)] |- _] => rewrite update_FOL_LAM in H
  | [H: ~ In _ (binder_l _)  |- _ ] => rewrite binder_l_not_In_FOL_LAM in H
  | [H: ~ In _ (binder_r _)  |- _ ] => rewrite  binder_r_not_In_FOL_LAM in H
  | [H: In ( _ ,_ , _ )  _  |- _ ] => rewrite  binder_list_In_FOL_LAM in H
  | [H: context [free_occur _ _] |- _ ] => rewrite  free_occur_FOL_LAM in H
  | [H: context [term_occur _ _] |- _ ] => rewrite  term_occur_FOL_LAM in H
  | [H: context [task_term_occur _  _] |- _ ] => rewrite  task_term_occur_FOL_LAM in H
  | [H: context [st_FOL2LAM (reduce _ _)] |- _ ] => rewrite reduce_FOL_LAM in H
  | [H: context [variable_list  (_++_)] |- _ ] => rewrite variable_list_app in H
  | [H: context [predname_list  (_++_)] |- _ ] => rewrite predname_list_app in H
  | [H: context [prop_var _] |- _ ] => rewrite prop_var_FOL_LAM2 in H
  | [H: context [tm_var _ ] |- _ ] => rewrite  tm_var_FOL_LAM2 in H
  | [H: context [task_var _] |- _ ] => rewrite task_var_FOL_LAM2 in H
  | [H: context [term2tm (term_sub _ _)] |- _ ] => rewrite term_sub_FOL_LAM in H
  | [H: context [prop2tm (prop_sub _ _)] |- _ ] => rewrite prop_sub_FOL_LAM in H
  | [|- term_alpha_eq _ _ _ ] => rewrite term_alpha_eq_FOL_LAM 
  | [|- alpha_eq _ _ _]=> rewrite alpha_eq_FOL_LAM 
  | [|- aeq _ _ ] => rewrite aeq_FOL_LAM 
  | [|- context [binder_list_FOL2LAM (update _ _ _)] ] => rewrite  update_FOL_LAM 
  | [|- context [free_occur _ _] ] => rewrite  free_occur_FOL_LAM 
  | [|- context [term_occur _ _] ] => rewrite  term_occur_FOL_LAM 
  | [|- context [task_term_occur _  _] ] => rewrite task_term_occur_FOL_LAM 
  | [|- context [st_FOL2LAM (reduce _ _)] ] => rewrite  reduce_FOL_LAM
  | [|- context [variable_list  (_++_)] ] => rewrite variable_list_app 
  | [|- context [predname_list  (_++_)] ] => rewrite predname_list_app 
  | [|- context [prop_var _]  ] => rewrite prop_var_FOL_LAM2
  | [|- context [tm_var _]  ] => rewrite  tm_var_FOL_LAM2
  | [|- context [task_var _] ] => rewrite task_var_FOL_LAM2
  | [|- context [term2tm (term_sub _ _)]  ] => rewrite term_sub_FOL_LAM 
  | [|- context [prop2tm (prop_sub _ _)]  ] => rewrite prop_sub_FOL_LAM 
  | [|- ~ In _ (binder_l _)  ] => rewrite binder_l_not_In_FOL_LAM 
  | [|- ~ In _ (binder_r _) ] => rewrite binder_r_not_In_FOL_LAM 
  | [|- In ( _ , _ , _ )  _  ] => rewrite binder_list_In_FOL_LAM
  end.

Corollary aeq_refl: Reflexive aeq.
Proof. unfold Reflexive. intros. FOL2LAM. aeq_solve. Qed.

Corollary aeq_sym: Symmetric aeq.
Proof. unfold Symmetric. intros. FOL2LAM. aeq_solve. Qed.

Corollary aeq_trans: Transitive aeq.
Proof. unfold Transitive. intros. FOL2LAM. aeq_solve. Qed. 

Add Relation prop aeq reflexivity proved by aeq_refl symmetry proved by aeq_sym 
        transitivity proved by aeq_trans as aeq_equivalence.
        
Corollary aeq_PAnd: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PAnd P1 Q1) (PAnd P2 Q2).
Proof. intros. FOL2LAM. simpl. aeq_solve. Qed. 

Corollary aeq_POr: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (POr P1 Q1) (POr P2 Q2).
Proof. intros. FOL2LAM. simpl. aeq_solve. Qed. 

Corollary aeq_PImpl: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PImpl P1 Q1) (PImpl P2 Q2).
Proof. intros. FOL2LAM. simpl. aeq_solve. Qed.

Corollary aeq_PIff: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PIff P1 Q1) (PIff P2 Q2).
Proof. intros. FOL2LAM. simpl. aeq_solve. Qed.  

Corollary aeq_PNot: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PAnd P1 Q1) (PAnd P2 Q2).
Proof. intros. FOL2LAM. simpl. aeq_solve. Qed.

Corollary aeq_PForall: forall x P1 P2,
  aeq P1 P2 ->
  aeq (PForall x P1) (PForall x P2).
Proof. intros. FOL2LAM. simpl. aeq_solve. Qed.

Corollary aeq_PExists: forall x P1 P2,
  aeq P1 P2 ->
  aeq (PExists x P1) (PExists x P2).
Proof. intros. FOL2LAM. simpl. aeq_solve. Qed.

Ltac baeq:=
  repeat match goal with
   | H: context[alpha_eq nil ?t1 ?t2] |- _  => let ph:=fresh "H" in 
                                                  assert (alpha_eq nil t1 t2 = aeq t1 t2) as ph;
                                                  [reflexivity| rewrite ph in H; clear ph]
   | |- alpha_eq nil ?t1 ?t2 => let ph:=fresh "H" in 
                                  assert (alpha_eq nil t1 t2 = aeq t1 t2) as ph;
                                  [reflexivity| rewrite ph;clear ph]
   | H: aeq ?t1 ?t2 |- aeq ?t1 ?t2 => exact H
   | |- aeq ?t ?t => reflexivity
   | H: aeq ?t1 ?t2 |- aeq ?t2 ?t1 => symmetry
(*    | [H:aeq (abs ?s ?t1)(abs ?s ?t2) |- aeq ?t1 ?t2] => apply remove_bind_aeq in H;tauto *)
(*    | [|- aeq (subst ?st _) (subst ?st _)] => apply subst_same_st_aeq *)
   | H: aeq ?t1 ?t2 |- aeq ?t1 ?t3 => transitivity  t2;[| clear H]
   | H: aeq ?t1 ?t2 |- aeq ?t3 ?t1 => transitivity  t2;[clear H|]
   | H: aeq ?t2 ?t1 |- aeq ?t1 ?t3 => transitivity  t2;[| clear H]
   | H: aeq ?t2 ?t1 |- aeq ?t3 ?t1 => transitivity t2;[clear H|]
(*    | [H: free_occur ?x ?t1 = ?n |- free_occur ?x ?t2 = ?n] => rewrite aeq_free_occur with x t2 t1;[exact H|]
   | [|- free_occur ?s _ = free_occur ?s _] => apply aeq_free_occur *)
   | |- aeq (PForall ?s ?t1) (PForall ?s ?t2) => apply aeq_PForall
   | |- aeq (PExists ?s ?t1) (PExists ?s ?t2) => apply aeq_PExists
   | |- aeq (PAnd _ _) (PAnd _ _) => apply aeq_PAnd
   | |- aeq (POr _ _) (POr _ _) => apply aeq_POr
   | |- aeq (PImpl _ _) (PImpl _ _) => apply aeq_PImpl
   | |- aeq (PIff _ _) (PIff _ _) => apply aeq_PIff
   | |- aeq  (PNot _) (PNot _) => apply aeq_PNot 
   | |- _ => try tauto
  end.

End DemoBasic.