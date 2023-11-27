Require Import Coq.Sorting.Permutation.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationClasses.
Require Import Operators_Properties.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import FV.Demo.Sugar.Sugar.
Require Import FV.Demo.Lambda.
Require Import FV.utils.

Module DemoSugarLambda.
Import LAM.
Include DemoSugarFOL.

Fixpoint term2tm (t:term):tm:=
 match t with
 | empty_set =>cons iempty
 | singleton x => app (cons isingleton) (term2tm x)
 | var x => LAM.var (uvar x)
 | intersection x y => app (cons iintersection) (app (term2tm x) (term2tm y))
 | union x y => app (cons iunion) (app (term2tm x) (term2tm y))
 end.
 
Fixpoint atom2tm (a:atom):tm:=
  match a with
  | APred r =>  LAM.var (upred r)
  | AApp a0 t => app (atom2tm a0) (term2tm t)
  end. 
  
Fixpoint tm_add_binders (xs: list V.t) (t: tm):=
  match xs with
  | nil => t
  | x::xs0 => abs (uvar x) (tm_add_binders xs0 t)
  end.
 
Lemma tm_add_binders_bstar: forall xs t1 t2,
  bstar  t1 t2 ->
  bstar (tm_add_binders xs t1) (tm_add_binders xs t2).
Proof. intros. induction xs; simpl; check_bstar. Qed.
 
 Fixpoint prop2tm (d:prop):tm:=
  match d with
  | PEq t1 t2 => app (cons iPEq) (app (term2tm t1) (term2tm t2))
  | PRel t1 t2 => app (cons iPRel) (app (term2tm t1) (term2tm t2))
  | PAtom a =>  atom2tm a
  | PFalse => cons iPFalse
  | PTrue => cons iPTrue
  | PNot P => app (cons iPNot) (prop2tm P)
  | PAnd P1 P2 => app (cons iPAnd) (app (prop2tm P1) (prop2tm P2))
  | POr P1 P2 => app (cons iPOr) (app (prop2tm P1) (prop2tm P2))
  | PImpl P1 P2 => app (cons iPImpl) (app (prop2tm P1) (prop2tm P2))
  | PIff P1 P2 => app (cons iPIff) (app (prop2tm P1) (prop2tm P2))
  | PForall x P => app (cons iPForall) (abs (uvar x) (prop2tm P))
  | PExists x P => app (cons iPExists) (abs (uvar x) (prop2tm P))
  | PPredDef r xs P Q =>  app (abs (upred r) (prop2tm Q)) (tm_add_binders xs (prop2tm P))
end.

Fixpoint abs2vs (t:tm): list V.t:=
  match t with
  | abs (uvar x) t0 => x:: (abs2vs t0)
  | _ => nil
  end.
  
Fixpoint remove_abs (t:tm): tm:=
  match t with
  | abs (uvar _ ) t0 => remove_abs t0
  | _ => t
  end.

Ltac destruct_name:=
  destruct_eq_dec; 
  repeat match goal with
  | H: ?t = ?t |- _ => clear H
  | H: context [pred_pred_occur _ _] |- _ => unfold pred_pred_occur in H
  | H: context [var_occur _ _] |- _ => unfold var_occur in H
  | H: context [R.eq_dec ?a ?b] |- _  => destruct (R.eq_dec a b) in H; subst
  | H: context [V.eq_dec ?a ?b] |- _ => destruct (V.eq_dec a b) in H; subst
  | |- context [pred_pred_occur _ _]  => unfold pred_pred_occur
  | |- context [var_occur _ _] => unfold var_occur 
  | |- context [R.eq_dec ?a ?b] => destruct (R.eq_dec a b); subst
  | |- context [V.eq_dec ?a ?b] => destruct (V.eq_dec a b); subst
  end; try congruence; try tauto.

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

Fixpoint tm2atom (t: tm): option atom:=
  match t with
  | LAM.var (upred r) => Some (APred r)
  | app t1 t2 => match tm2atom t1, tm2term t2 with
                         | Some a1, Some u1 => Some (AApp a1 u1)
                         | _ , _ => None
                         end
  | _ => None
  end.
  
Fixpoint tm2prop (t:tm): option prop:=
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
  | app (abs (upred r) Q0) P0 => let xs:= abs2vs P0 in
                                                  let Pt:= remove_abs P0 in
                                                  match tm2prop Q0, tm2prop Pt with
                                                  | Some Q, Some P => Some (PPredDef r xs P Q)
                                                  | _ , _ => None
                                                  end
  
  | _ => match tm2atom t with
             | Some a => Some (PAtom a)
             | _ => None
             end
end.

Definition subst_pair_FOL2LAM (st:subst_pair):ustr* LAM.tm:=
  match st with
  | svar x t => (uvar x, term2tm t)
  | spred r1 r2 => (upred r1, LAM.var (upred r2))
  | sprop r xs P => (upred r, tm_add_binders xs (prop2tm P))
  end. 
  
Definition st_FOL2LAM (st:subst_task): LAM.subst_task:=
  map subst_pair_FOL2LAM st.

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

Lemma tm2prop_tm2atom: forall t a,
  tm2prop t = Some (PAtom a) <->
  tm2atom t = Some a.
Proof.
  split; intros. 
  ++ destruct t.
  + destruct c; discriminate H.
  + destruct s. discriminate H. simpl in H. inversion H. subst a. reflexivity.
  + destruct t1.
      - destruct c; try discriminate H; destruct t2; try discriminate H.  
         * simpl in H. destruct (tm2term t2_1); destruct (tm2term t2_2); discriminate H.
         * simpl in H. destruct (tm2term t2_1); destruct (tm2term t2_2); discriminate H.
         * simpl in H. destruct c; discriminate H.
         * simpl in H. destruct s; discriminate H.
         * remember (app t2_1 t2_2) as t. simpl in H. destruct (tm2prop t); discriminate H.
         * simpl in H. destruct (tm2prop t2_1); destruct (tm2prop t2_2); discriminate H.
         * simpl in H. destruct (tm2prop t2_1); destruct (tm2prop t2_2); discriminate H.
         * simpl in H. destruct (tm2prop t2_1); destruct (tm2prop t2_2); discriminate H.
         * simpl in H. destruct (tm2prop t2_1); destruct (tm2prop t2_2); discriminate H.
         * simpl in H. destruct v. destruct (tm2prop t2); discriminate H. discriminate H.
         * simpl in H. destruct v. destruct (tm2prop t2); discriminate H. discriminate H.
     -  simpl in H. destruct s. discriminate H. destruct (tm2term t2) eqn: H1. inversion H. subst a.
         repeat_rewrite. discriminate H.
     -  simpl in H. destruct (tm2atom t1_1) eqn: H1;[|discriminate H].
        destruct (tm2term t1_2) eqn: H2; [|discriminate H].
        destruct (tm2term t2) eqn:H3;[| discriminate H]. 
        inversion H. subst a. repeat_rewrite.
     - simpl in H. destruct v. discriminate H. destruct (tm2prop t1); destruct (tm2prop (remove_abs t2) ); discriminate H.
  + discriminate H.
  ++ destruct t; intros; try discriminate H.
  + destruct s. discriminate H. simpl in H. inversion H. subst a. reflexivity.
  + simpl in H.  destruct (tm2atom t1) eqn: H1; destruct (tm2term t2) eqn: H2; try discriminate H.
      inversion H. subst a. clear H.
      simpl. repeat rewrite H2. destruct t1; try discriminate H1.
      - rewrite H1. reflexivity.
      - rewrite H1. reflexivity.
Qed.

Lemma atom2tm_tm2atom: forall a,
  tm2atom (atom2tm a) = Some a.
Proof.
  intros. induction a. reflexivity.
  simpl. rewrite IHa. rewrite term2tm_tm2term. easy.
Qed.

Lemma atom2tm_tm2prop: forall (a:atom),
  tm2prop (atom2tm a) = Some (PAtom a).
Proof.
  intros. induction a.
  + reflexivity.
  + apply tm2prop_tm2atom in IHa. apply tm2prop_tm2atom.
      simpl. rewrite IHa. rewrite term2tm_tm2term. reflexivity.
Qed.

Lemma term2tm_injective: forall t1 t2,
  term2tm t1 = term2tm t2 -> t1 = t2.
Proof.
  induction t1; destruct t2; intros; try discriminate H.
  + simpl in H.  congruence.
  + easy.
  + simpl in H. injection H as H. f_equal. auto.
  + injection H as H. f_equal; auto.
  + injection H as H. f_equal; auto.
Qed.

Lemma atom2tm_injective: forall a1 a2,
  atom2tm a1 = atom2tm a2 -> a1 = a2.
Proof.
  induction a1; destruct a2; intros; try discriminate H.
  + simpl in H. congruence.
  + injection H as H. apply term2tm_injective in H0. apply IHa1 in H. congruence.
Qed. 
  

Lemma tm_add_binders_remove_abs: forall xs P,
  remove_abs (tm_add_binders xs (prop2tm P)) = prop2tm P.
Proof.
  intros. induction xs.
  + simpl. destruct P; simpl; try  repeat rewrite term2tm_tm2term; try reflexivity.
      destruct a; easy.
  + easy.
Qed. 

Lemma tm_add_binders_abs2vs: forall xs P,
  abs2vs (tm_add_binders xs (prop2tm P)) = xs.
Proof.
  intros. induction xs.
  + simpl. destruct P; simpl; try  repeat rewrite term2tm_tm2term; try reflexivity.
      destruct a; easy.
  + simpl. congruence.
Qed.


Lemma update_FOL_LAM: forall x y bd,
 update x y bd = LAM.update x y bd.
 Proof.
    induction bd.
    + easy.
    + destruct a as [ [? ?] ?]. simpl. rewrite IHbd. 
        assert (ustr_occur x u = LAM.var_occur x u).
        { destruct x; destruct u; unfold ustr_occur; unfold LAM.var_occur.
          destruct (V.eq_dec v v0); destruct (var_eq_dec v v0); congruence.
          destruct (var_eq_dec v (upred r)) eqn :E ;[discriminate e| easy].
          destruct (var_eq_dec (upred r) v ) eqn :E ;[discriminate e| easy].
          destruct (R.eq_dec r r0); destruct (var_eq_dec (upred r) (upred r0)); congruence. }
       assert (ustr_occur y u0 = LAM.var_occur y u0).
        { destruct y; destruct u0; unfold ustr_occur; unfold LAM.var_occur.
          destruct (V.eq_dec v v0); destruct (var_eq_dec v v0); congruence.
          destruct (var_eq_dec v (upred r)) eqn :E ;[discriminate e| easy].
          destruct (var_eq_dec (upred r) v ) eqn :E ;[discriminate e| easy].
          destruct (R.eq_dec r r0); destruct (var_eq_dec (upred r) (upred r0)); congruence. }
        rewrite H. rewrite H0. easy.
Qed. 

Lemma tm_add_binders_aeq: forall xs1 xs2 bd t1 t2,
   length xs1 = length xs2 ->
   (LAM.alpha_eq bd (tm_add_binders xs1 t1) (tm_add_binders xs2 t2) <->
   LAM.alpha_eq (var_list_update xs1 xs2 bd) t1 t2 ).
Proof.
  split;intros. 
  + revert xs2 bd H H0. induction xs1; intros; destruct xs2; try discriminate H.
    - easy. 
    - simpl in H0. simpl. apply IHxs1. now injection H.
      inversion H0; subst. now rewrite <- update_FOL_LAM in H7.
  +  revert xs2 bd H H0. induction xs1; intros; destruct xs2; try discriminate H.
    - easy.
    - simpl. constructor. easy. apply IHxs1. now injection H. simpl in H0. now rewrite <- update_FOL_LAM.
Qed.      

Lemma prop2tm_tm2prop: forall (P:prop),
  tm2prop (prop2tm P) = Some P.
Proof. 
  induction P; repeat_rewrite.
  + rewrite 2 term2tm_tm2term. easy.
  + rewrite 2 term2tm_tm2term. easy.
  + apply atom2tm_tm2prop.
  + rewrite tm_add_binders_remove_abs. rewrite IHP1. 
      rewrite tm_add_binders_abs2vs. easy.
Qed.

Lemma term_ustr_FOL_LAM: forall t,
  term_ustr t = LAM.tm_var (term2tm t).
Proof. induction t; repeat_rewrite. Qed.

Lemma atom_ustr_FOL_LAM: forall a,
  atom_ustr a = LAM.tm_var (atom2tm a).
Proof. induction a; repeat_rewrite. now rewrite term_ustr_FOL_LAM. Qed.

Lemma tm_add_binders_tm_var: forall xs t,
  tm_var (tm_add_binders xs t) = (map uvar xs) ++ tm_var t.
Proof. intros. induction xs. easy. simpl. now f_equal. Qed.

Lemma prop_ustr_FOL_LAM: forall P,
  prop_ustr P = LAM.tm_var (prop2tm P).
Proof. 
  induction P; repeat_rewrite; try now rewrite 2 term_ustr_FOL_LAM.  
  apply atom_ustr_FOL_LAM. rewrite tm_add_binders_tm_var. easy.
Qed.

Lemma task_ustr_FOL_LAM: forall st,
  task_ustr st = LAM.task_var (st_FOL2LAM st).
Proof.
  induction st. easy.
  destruct a.
  + simpl. rewrite IHst. rewrite term_ustr_FOL_LAM. easy.
  + simpl. rewrite IHst. easy. 
  + simpl. rewrite tm_add_binders_tm_var. rewrite prop_ustr_FOL_LAM. now rewrite IHst. 
Qed.

Lemma term_occur_FOL_LAM: forall (x: V.t) t,
  term_occur x t = LAM.free_occur (uvar x) (term2tm t).
Proof. 
  induction t; repeat_rewrite. 
  unfold LAM.var_occur. 
  destruct (var_eq_dec x v); destruct (V.eq_dec x v); congruence.
Qed.

Lemma atom_occur_FOL_LAM: forall (x:V.t) a,
  atom_occur x a = LAM.free_occur (uvar x)(atom2tm a).
Proof.
  intros. induction a.
  + simpl. unfold LAM.var_occur. destruct (var_eq_dec x (upred r)).  discriminate e. easy.
  + simpl. rewrite term_occur_FOL_LAM. rewrite IHa. easy.
Qed.

Lemma free_occur_tm_add_binder_In: forall x xs t,
  In x xs ->
  LAM.free_occur (uvar x) (tm_add_binders xs t) = 0.
Proof.
  intros.  induction xs. inversion H.
  destruct H. subst a. simpl. destruct (var_eq_dec x x); congruence. simpl.
  destruct (var_eq_dec x a); tauto.
Qed.

Lemma free_occur_tm_add_binder_not_In: forall x xs t,
  ~  In x xs ->
  LAM.free_occur (uvar x) (tm_add_binders xs t) = LAM.free_occur (uvar x) t.
Proof.
  intros.  induction xs. reflexivity.
  apply not_in_cons in H. destruct H. apply IHxs in H0. clear IHxs.
  simpl. destruct (var_eq_dec x a);[congruence|assumption].
Qed.

Lemma free_occur_FOL_LAM: forall (x:V.t) P,
 free_occur x P = LAM.free_occur (uvar x) (prop2tm P).
Proof. 
  induction P; repeat_rewrite. 
  + now rewrite 2 term_occur_FOL_LAM.
  + now rewrite 2 term_occur_FOL_LAM.
  + apply atom_occur_FOL_LAM.
  + destruct (V.eq_dec x x0); destruct (var_eq_dec x x0); congruence.
  + destruct (V.eq_dec x x0); destruct (var_eq_dec x x0); congruence.
  + destruct (var_eq_dec x (upred r)). discriminate e.
      destruct (in_vars_dec x xs) eqn:E.
      - simpl. assert (In x xs) by tauto. apply in_vars_true in H.
        rewrite H. now rewrite free_occur_tm_add_binder_In.
      - assert (~In x xs). assumption. apply in_vars_false in H.
        rewrite H. rewrite (free_occur_tm_add_binder_not_In _ _ _ n0).
        apply PeanoNat.Nat.add_comm.  
Qed.

Lemma term2tm_pred_not_occur: forall r t,
  LAM.free_occur (upred r) (term2tm t) = 0.
Proof.
  induction t; simpl; try congruence.
  + unfold LAM.var_occur. destruct (var_eq_dec (upred r) (uvar v)); congruence.
  + rewrite IHt1. now rewrite IHt2. 
  + rewrite IHt1. now rewrite IHt2.
Qed. 

Lemma task_term_occur_FOL_LAM: forall (x:V.t) st,
 task_term_occur x st = LAM.st_tm_occur (uvar x) (st_FOL2LAM st).
Proof.
  induction st. easy. destruct a.
  + simpl. rewrite IHst. rewrite term_occur_FOL_LAM. easy.
  + simpl. rewrite IHst. unfold LAM.var_occur. destruct (var_eq_dec x (upred r0)).
     discriminate e. easy.
  + simpl. destruct (in_vars_dec x xs) eqn:E.
      - rewrite IHst. assert (In x xs) by tauto.
        apply in_vars_true in H. rewrite H.
         now rewrite free_occur_tm_add_binder_In.
      - rewrite IHst. assert (~ In x xs). assumption.
        apply in_vars_false in H. rewrite H.
        rewrite free_occur_tm_add_binder_not_In. 
        rewrite free_occur_FOL_LAM. easy. easy.
Qed.

Lemma subst_task_Permutation_FOL_LAM: forall st1 st2,
  Permutation st1 st2 -> Permutation (st_FOL2LAM st1) (st_FOL2LAM st2).
Proof.  
  intros. induction H. 
     - constructor.
     - simpl. destruct x; now constructor.
     - simpl. destruct x; destruct y; now constructor.
     - econstructor. apply IHPermutation1. easy.
Qed.
    
Lemma tm_add_binders_pred_occur: forall r xs d,
  LAM.free_occur (upred r) (tm_add_binders xs (prop2tm d)) = LAM.free_occur (upred r) (prop2tm d).
Proof. induction xs; intros. easy. simpl. destruct_name.  Qed.

Lemma pred_atom_occur_FOL_LAM: forall (x:V.t) a,
  pred_atom_occur x a = LAM.free_occur (upred x)(atom2tm a).
Proof.
  induction a.
  - destruct_name.
  - simpl. rewrite term2tm_pred_not_occur. now rewrite PeanoNat.Nat.add_0_r.
Qed.   

Lemma pred_free_occur_FOL_LAM: forall (x:R.t) P,
 pred_free_occur x P = LAM.free_occur (upred x) (prop2tm P).
Proof.
     induction P; repeat_rewrite. 
     + now repeat rewrite term2tm_pred_not_occur.
     + now repeat rewrite term2tm_pred_not_occur.
     + apply pred_atom_occur_FOL_LAM.
     + destruct_name. 
     + destruct_name.
     + destruct_name. now rewrite tm_add_binders_pred_occur.
         rewrite tm_add_binders_pred_occur. apply PeanoNat.Nat.add_comm.
Qed.

Lemma pred_task_term_occur_FOL_LAM: forall (x:V.t) st,
 pred_task_term_occur x st = LAM.st_tm_occur (upred x) (st_FOL2LAM st).
Proof.
  induction st. easy. destruct a; simpl.
  + now rewrite term2tm_pred_not_occur.
  + rewrite IHst. unfold pred_pred_occur. unfold LAM.var_occur. destruct_name.
  + rewrite IHst. rewrite tm_add_binders_pred_occur. now rewrite pred_free_occur_FOL_LAM.
Qed.

Lemma reducev_FOL_LAM: forall x st,
  st_FOL2LAM (reducev x st) = LAM.reduce (uvar x) (st_FOL2LAM st).
Proof.
  induction st. easy.
  destruct a; simpl; try rewrite IHst; destruct_name. simpl. now rewrite IHst.
Qed.

Lemma reducer_FOL_LAM: forall r st,
  st_FOL2LAM (reducer r st) = LAM.reduce (upred r) (st_FOL2LAM st).
Proof.
  induction st. easy.
  destruct a; simpl; try rewrite IHst; destruct_name; simpl; now rewrite IHst. 
Qed.

Lemma newv_FOL_LAM: forall l,
  newv l = V.list_new_name (variable_list l).
Proof. induction l. easy. unfold newv. destruct a;easy. Qed.

Lemma newr_FOL_LAM: forall l,
  newr l = R.list_new_name (predname_list l).
Proof. induction l. easy. unfold newv. destruct a;easy. Qed.

Local Ltac LAM2FOL_aux1:=
  repeat match goal with
  | [H: context [LAM.free_occur (uvar _) (prop2tm _)] |- _ ] => rewrite <- free_occur_FOL_LAM in H
  | [H: context [LAM.free_occur (uvar _) (term2tm _)] |- _ ] => rewrite <- term_occur_FOL_LAM in H
  | [H: context [LAM.st_tm_occur (uvar _ ) (st_FOL2LAM _)] |- _ ] => rewrite <- task_term_occur_FOL_LAM in H
  | [H: context [LAM.st_tm_occur (upred _ ) (st_FOL2LAM _)] |- _ ] => rewrite <- pred_task_term_occur_FOL_LAM in H
  | [H: context [LAM.reduce (uvar _) (st_FOL2LAM _)] |- _ ] => rewrite <- reducev_FOL_LAM in H
  | [H: context [LAM.reduce (upred _) (st_FOL2LAM _)] |- _ ] => rewrite <- reducer_FOL_LAM in H
(*   | [H: context [variable_list  (_++_)] |- _ ] => rewrite variable_list_app in H
  | [H: context [predname_list  (_++_)] |- _ ] => rewrite predname_list_app in H *)
  | [H: context [LAM.tm_var (prop2tm _ )] |- _ ] => rewrite <- prop_ustr_FOL_LAM in H
  | [H: context [LAM.tm_var (term2tm _ )] |- _ ] => rewrite <- term_ustr_FOL_LAM in H
  | [H: context [LAM.task_var (st_FOL2LAM _)] |- _ ] => rewrite <- task_ustr_FOL_LAM in H
  | [|- context [LAM.free_occur (uvar _) (prop2tm _)] ] => rewrite <- free_occur_FOL_LAM 
  | [|- context [LAM.free_occur (uvar _) (term2tm _)] ] => rewrite <- term_occur_FOL_LAM 
  | [|- context [LAM.st_tm_occur (uvar _ ) (st_FOL2LAM _)] ] => rewrite <- task_term_occur_FOL_LAM 
  | [|- context [LAM.st_tm_occur (upred _ ) (st_FOL2LAM _)] ] => rewrite <- pred_task_term_occur_FOL_LAM 
  | [|- context [LAM.reduce (uvar _) (st_FOL2LAM _)] ] => rewrite <- reducev_FOL_LAM
  | [|- context [LAM.reduce (upred _) (st_FOL2LAM _)] ] => rewrite <- reducer_FOL_LAM
(*   | [|- context [variable_list  (_++_)] ] => rewrite variable_list_app 
  | [|- context [predname_list  (_++_)] ] => rewrite predname_list_app  *)
  | [|- context [LAM.tm_var (prop2tm _ )]  ] => rewrite <- prop_ustr_FOL_LAM
  | [|- context [LAM.tm_var (term2tm _ )]  ] => rewrite <- term_ustr_FOL_LAM 
  | [|- context [LAM.task_var (st_FOL2LAM _)] ] => rewrite <- task_ustr_FOL_LAM
  end.

Lemma term_sub_FOL_LAM: forall t st,
  term2tm (term_sub st t) = subst (st_FOL2LAM st) (term2tm t).
Proof.
  induction t; intros; simpl; try congruence.
  induction st. easy. destruct a; destruct_name.
Qed.

Lemma tm_add_binders_subst: forall xs st d,
  subst (st_FOL2LAM st) (tm_add_binders xs (prop2tm d)) = 
  tm_add_binders (vars_new_xs d xs st) (subst (st_FOL2LAM (vars_new_st d xs st)) (prop2tm d)).
Proof.
  induction xs; intros.
  + easy.
  + simpl. LAM2FOL_aux1. destruct (task_term_occur a (reducev a st)).
      - simpl. now rewrite IHxs.
      - rewrite newv_FOL_LAM. simpl. rewrite <- IHxs. repeat rewrite tm_add_binders_tm_var.
        simpl. LAM2FOL_aux1. now repeat rewrite <- app_assoc.
Qed. 

Lemma atom_var_sub_FOL_LAM: forall a st,
  Forall only_var_sub st ->
  atom2tm (atom_var_sub st a) = subst (st_FOL2LAM st) (atom2tm a).
Proof.
  intros. revert st H. induction a; intros.
  + simpl. induction st.
      - easy.
      - forall_cons H. inversion H; subst. simpl. destruct_name.
  + simpl. rewrite term_sub_FOL_LAM. now rewrite IHa.
Qed.

Lemma prop_var_sub_FOL_LAM: forall p st,
  Forall only_var_sub st ->
  prop2tm (prop_var_sub st p) = subst (st_FOL2LAM st) (prop2tm p).
Proof.
  intros. revert st H. induction p; intros; simpl; try repeat rewrite term_sub_FOL_LAM; 
  try rewrite IHp; try rewrite IHp1; try rewrite IHp2; try congruence.
  + now apply atom_var_sub_FOL_LAM.
  + LAM2FOL_aux1. destruct ( task_term_occur x (reducev x st)).
      -  simpl. repeat f_equal. apply IHp. now apply reducev_Forall.
      - simpl. repeat f_equal. apply IHp.  apply Forall_cons. constructor. now apply reducev_Forall.
  + LAM2FOL_aux1. destruct ( task_term_occur x (reducev x st)).
      -  simpl. repeat f_equal. apply IHp. now apply reducev_Forall.
      - simpl. repeat f_equal. apply IHp.  apply Forall_cons. constructor. now apply reducev_Forall.
  + LAM2FOL_aux1. 
      rewrite reducer_only_var_sub. rewrite pred_task_term_occur_only_var_sub. f_equal.
      now rewrite tm_add_binders_subst.  easy. easy. 
  + now apply vars_new_st_only_var_sub.
Qed.

Lemma term_alpha_eq_FOL_LAM: forall bd t1 t2,
  term_alpha_eq bd t1 t2 <-> LAM.alpha_eq bd (term2tm t1) (term2tm t2).
Proof.
  split; intros.
  + induction H; simpl.
      - constructor.
      - now apply str_aeq1.
      - now apply str_aeq2.
      - constructor; [constructor|easy].
      - constructor; [constructor|constructor;easy].
      - constructor; [constructor|constructor;easy].
  + revert t2 H. induction t1; intros; inversion H; subst. 
      - destruct t2; inversion H1; subst.  now constructor.
      - destruct t2; inversion H1; subst. now constructor.
      - destruct t2; inversion H3; subst. now constructor.
      - inversion H4; subst. destruct t2; inversion H3; subst. constructor. now apply IHt1. 
      - inversion H4; subst. inversion H5; subst. destruct t2;inversion H3; subst.
        constructor. now apply IHt1_1. now apply IHt1_2.
      - inversion H4; subst. inversion H5; subst. destruct t2;inversion H3; subst.
        constructor. now apply IHt1_1. now apply IHt1_2.
Qed.

Lemma atom_alpha_eq_FOL_LAM: forall bd a1 a2,
  atom_alpha_eq bd a1 a2 <-> LAM.alpha_eq bd (atom2tm a1) (atom2tm a2).
Proof.
  split; intros.
  + induction H.
      - now constructor.
      - now constructor 3.
      - simpl. constructor. easy. now apply term_alpha_eq_FOL_LAM.
  + revert a2 H. induction a1; intros; inversion H; subst.
      - destruct a2; inversion H1; subst. now constructor.
      - destruct a2; inversion H1; subst. now constructor.
      - destruct a2; inversion H3; subst. constructor. now apply IHa1. now apply term_alpha_eq_FOL_LAM.
Qed.    

Ltac disc_tm:=
  let a0:= fresh "a" in
  match goal with
  | [H: app (cons _ ) _ = atom2tm ?a |- _ ]=> destruct a as [? | a0] ; [discriminate H| destruct a0; discriminate H] 
  | [H: atom2tm ?a =  app (cons _ ) _|- _ ]=> destruct a as [? | a0] ; [discriminate H| destruct a0; discriminate H] 
  | [H: app (abs _ _ ) _ = atom2tm ?a |- _ ]=> destruct a as [? | a0] ; [discriminate H| destruct a0; discriminate H] 
  | [H: atom2tm ?a = app (abs _ _ ) _ |- _ ]=> destruct a as [? | a0] ; [discriminate H| destruct a0; discriminate H] 
  | [H: cons ?c = atom2tm ?a |- _ ] => destruct a; discriminate H
  | [H: atom2tm ?a = cons ?c |- _ ] => destruct a; discriminate H
  | [H: abs _ _ = atom2tm ?a |- _ ] => destruct a; discriminate H
  | [H: atom2tm ?a = abs _ _|- _ ] => destruct a; discriminate H
  end.


Lemma inversion_tm_add_binders_aeq: forall xs bd t1 t2,
  LAM.alpha_eq bd (tm_add_binders xs t1) t2 ->
  exists xs' t2' , length xs = length xs' /\ t2 = tm_add_binders xs' t2' /\ LAM.alpha_eq (var_list_update xs xs' bd) t1 t2'.
Proof.
  induction xs; intros.
  + exists nil. exists t2.  tauto.
  + simpl in H. destruct t2; try inversion H; subst. destruct v. 2:discriminate H4. rewrite <- update_FOL_LAM in H6.
      apply IHxs in H6. clear IHxs. destruct H6 as [xs' [t2' [H1 [H2 H3] ] ] ].
      exists (v::xs'). exists t2'. simpl. split. congruence. split. congruence. easy.
Qed.

Lemma tm_add_binders_on_prop_aeq_lemma: forall xs1 xs2 bd P1 P2,
    LAM.alpha_eq bd (tm_add_binders xs1 (prop2tm P1)) (tm_add_binders xs2 (prop2tm P2)) ->
    length xs1 = length xs2 /\  LAM.alpha_eq  (var_list_update xs1 xs2 bd) (prop2tm P1) (prop2tm P2).
Proof.
   intros. revert xs2 bd P1 P2 H.  induction xs1; destruct xs2; intros.
   + simpl in H. easy.
   + simpl in H. destruct P1; try inversion H. disc_tm.
   + simpl in H. destruct P2; try inversion H. disc_tm.
   + simpl in H. inversion H; subst. apply IHxs1 in H6.
      destruct H6. split. simpl. congruence. simpl. now rewrite <- update_FOL_LAM in H1.
Qed.


Lemma inversion_term2tm: forall bd t t0,
  LAM.alpha_eq bd (term2tm t) t0 ->
  exists t', t0 =  term2tm t' /\ term_alpha_eq bd t t'.
Proof.
  intros. revert t0 H. induction t; intros; inversion H; subst.
  + destruct s2; try discriminate H1. exists (var v0). split. easy. now constructor. 
  + exists (var v).  split. easy. now constructor.
  + exists empty_set. split. easy. constructor.
  + apply IHt in H5. destruct H5. inversion H3; subst. exists [[{x}]]%s. 
      destruct H0. split. simpl. congruence. now constructor.
  + inversion H3; subst. inversion H5; subst. apply IHt1 in H4. apply IHt2 in H7.  
      destruct H4 as [ ? [? ?] ]. destruct H7 as [? [? ?] ].
      exists [[x ∪ x0]]%s. split. simpl. congruence. now constructor.
  + inversion H3; subst. inversion H5; subst. apply IHt1 in H4. apply IHt2 in H7.  
      destruct H4 as [ ? [? ?] ]. destruct H7 as [? [? ?] ].
      exists [[x ∩ x0]]%s. split. simpl. congruence. now constructor.
Qed.
      
Lemma inversion_atom2tm: forall bd a t,
  LAM.alpha_eq bd (atom2tm a) t ->
  exists a', t= atom2tm a' /\ atom_alpha_eq bd a a'.
Proof.
  intros. revert t H. induction a; intros.
  + simpl in H. inversion H; subst.
      - destruct s2; try discriminate H1. exists (APred r0). split. easy. now constructor.
      - exists (APred r). split. easy. now constructor.
  + simpl in H. inversion H; subst. apply IHa in H3. destruct H3 as [a0 [H1 H2] ].
      apply inversion_term2tm in H5. destruct H5 as [? [? ?] ]. exists (AApp a0 x).
      split. simpl.  congruence. now constructor.
Qed.
       
Lemma alpha_eq_FOL_LAM: forall bd P1 P2,
  alpha_eq bd P1 P2 <-> LAM.alpha_eq bd (prop2tm P1) (prop2tm P2) .
Proof.
  split; intros.
  + induction H; simpl; try constructor;try constructor; try easy; try now apply term_alpha_eq_FOL_LAM.
     - now apply atom_alpha_eq_FOL_LAM.
     - now rewrite <- update_FOL_LAM.
     - now rewrite <- update_FOL_LAM.
     - now rewrite <- update_FOL_LAM. 
     - now rewrite tm_add_binders_aeq. 
  +  revert bd P2 H. induction P1; intros; inversion H; subst.
      - inversion H4; subst. inversion H5; subst. destruct P2;inversion H3; subst. constructor; now apply term_alpha_eq_FOL_LAM.
        disc_tm.
      - inversion H4; subst. inversion H5; subst. destruct P2;inversion H3; subst. constructor; now apply term_alpha_eq_FOL_LAM.
        disc_tm.
      - disc_tm. 
      - destruct P2; try discriminate H1. destruct a; try discriminate H0. destruct a0; try discriminate H2.
         constructor.  constructor. simpl in H0. simpl in H1. injection H0 as H0. injection H1 as H1. 
         rewrite <- H1. rewrite<-  H0. easy. discriminate H1. 
      - destruct a; try discriminate H0. destruct P2; try discriminate H1. destruct a; try discriminate H1.
        simpl in H0. simpl in H1. injection H0 as H0. injection H1 as H1. assert (r=r0) by congruence. subst r0. constructor.
        subst s. now constructor 2.
      - destruct a; try discriminate H0. simpl in H0. injection H0 as H0. subst t1. subst t2.
        apply inversion_atom2tm in H3. destruct H3 as [? [? ?] ]. 
        apply inversion_term2tm in H4. destruct H4 as [? [? ?] ]. subst t3. subst t4.
        destruct P2; try injection H1 as H1; try disc_tm; try discriminate H1.
        simpl in H1. destruct a0. discriminate H1. simpl in H1. injection H1 as H1. apply term2tm_injective in H0.  
        apply atom2tm_injective in H1. subst. constructor. now constructor. 
      - disc_tm.
      - destruct P2;inversion H3; subst. disc_tm.  constructor.
      - destruct P2;inversion H3; subst. disc_tm.  constructor.
      - inversion H4; subst. destruct P2; inversion H3; subst. disc_tm.  constructor. now apply IHP1.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. disc_tm. constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. disc_tm.  constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. disc_tm.  constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. disc_tm.  constructor. now apply IHP1_1. now apply IHP1_2.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. disc_tm.  constructor. 
        rewrite <- update_FOL_LAM in H8. auto.
      - inversion H4; subst. inversion H5; subst. destruct P2; inversion H3; subst. disc_tm. constructor.
        rewrite <- update_FOL_LAM in H8. auto.
      - inversion H4; subst. destruct x'. discriminate H6. destruct P2; inversion H3; subst. disc_tm.
        apply tm_add_binders_on_prop_aeq_lemma in H5. destruct H5. rewrite <- update_FOL_LAM in H8. 
        constructor. easy. auto. auto.
Qed.

Corollary aeq_FOL_LAM: forall P1 P2,
  aeq P1 P2 <-> LAM.aeq (prop2tm P1) (prop2tm P2).
Proof.  apply alpha_eq_FOL_LAM with (bd:=nil). Qed.

Ltac LAM2FOL:=
  repeat match goal with
  | [H: LAM.alpha_eq _ (term2tm _ ) (term2tm _) |- _ ] => rewrite <- term_alpha_eq_FOL_LAM in H
  | [H: LAM.alpha_eq _ (prop2tm _ ) (prop2tm _) |-_ ]=> rewrite <- alpha_eq_FOL_LAM in H
  | [H: LAM.aeq (prop2tm _ ) (prop2tm _ ) |- _ ] => rewrite <-aeq_FOL_LAM in H
  | [H: context [LAM.update (uvar _ ) (uvar _ )  _ ] |- _] => rewrite <- update_FOL_LAM in H
  | [H: context [LAM.free_occur (uvar _) (prop2tm _)] |- _ ] => rewrite <- free_occur_FOL_LAM in H
  | [H: context [LAM.free_occur (uvar _) (term2tm _)] |- _ ] => rewrite <- term_occur_FOL_LAM in H
  | [H: context [LAM.st_tm_occur (uvar _ )  _] |- _ ] => rewrite <- task_term_occur_FOL_LAM in H
  | [H: context [LAM.st_tm_occur (upred _) _]  |- _ ]=> rewrite <- pred_task_term_occur_FOL_LAM in H
  | [H: context [LAM.reduce (uvar _) (st_FOL2LAM _)] |- _ ] => rewrite <- reducev_FOL_LAM in H
  | [H: context [LAM.reduce (upred _) (st_FOL2LAM _)] |- _ ] => rewrite <- reducer_FOL_LAM in H
(*   | [H: context [variable_list  (_++_)] |- _ ] => rewrite variable_list_app in H
  | [H: context [predname_list  (_++_)] |- _ ] => rewrite predname_list_app in H *)
  | [H: context [variable_list (LAM.tm_var (prop2tm _ ))] |- _ ] => rewrite <- prop_ustr_FOL_LAM in H
  | [H: context [variable_list (LAM.tm_var (term2tm _ ))] |- _ ] => rewrite <- term_ustr_FOL_LAM in H
  | [H: context [variable_list (LAM.task_var (st_FOL2LAM _))] |- _ ] => rewrite <- task_ustr_FOL_LAM in H
  | [H: context [subst (st_FOL2LAM _) (term2tm _)] |- _ ] => rewrite <- term_sub_FOL_LAM in H
  | [|- LAM.alpha_eq  _ (term2tm _ ) (term2tm _)  ] => rewrite <- term_alpha_eq_FOL_LAM 
  | [|-  LAM.alpha_eq _ (prop2tm _ ) (prop2tm _) ]=> rewrite <- alpha_eq_FOL_LAM 
  | [|- LAM.aeq (prop2tm _ ) (prop2tm _) ] => rewrite <- aeq_FOL_LAM 
  | [|- context [LAM.update _ _  _ ] ] => rewrite <- update_FOL_LAM 
  | [|- context [LAM.free_occur (uvar _) (prop2tm _)] ] => rewrite <- free_occur_FOL_LAM 
  | [|- context [LAM.free_occur (uvar _) (term2tm _)] ] => rewrite <- term_occur_FOL_LAM 
  | [|- context [LAM.st_tm_occur (uvar _ ) (st_FOL2LAM _)] ] => rewrite <- task_term_occur_FOL_LAM 
  | [|- context [LAM.st_tm_occur (upred _) (st_FOL2LAM _)] ] => rewrite <- pred_task_term_occur_FOL_LAM
  | [|- context [LAM.reduce (uvar _) (st_FOL2LAM _)] ] => rewrite <- reducev_FOL_LAM
  | [|- context [LAM.reduce (upred _) (st_FOL2LAM _)] ] => rewrite <- reducer_FOL_LAM
(*   | [|- context [variable_list  (_++_)] ] => rewrite variable_list_app 
  | [|- context [predname_list  (_++_)] ] => rewrite predname_list_app  *)
  | [|- context [variable_list (LAM.tm_var (prop2tm _ ))]  ] => rewrite <- prop_ustr_FOL_LAM
  | [|- context [variable_list (LAM.tm_var (term2tm _ ))]  ] => rewrite <- term_ustr_FOL_LAM
  | [|- context [variable_list (LAM.task_var (st_FOL2LAM _))] ] => rewrite <- task_ustr_FOL_LAM
  | [|- context [subst (st_FOL2LAM _) (term2tm _)]  ] => rewrite <- term_sub_FOL_LAM 
  end.


Ltac FOL2LAM:=
  repeat match goal with
  | [H: term_alpha_eq _ _ _ |- _ ] => rewrite term_alpha_eq_FOL_LAM in H
  | [H: alpha_eq _ _ _ |-_ ]=> rewrite alpha_eq_FOL_LAM in H
  | [H: aeq _ _ |- _ ] => rewrite aeq_FOL_LAM in H
  | [H: context [update _  _   _ ] |- _] => rewrite update_FOL_LAM in H
  | [H: context [free_occur _ _] |- _ ] => rewrite  free_occur_FOL_LAM in H
  | [H: context [pred_free_occur _ _] |- _ ] => rewrite  pred_free_occur_FOL_LAM in H
  | [H: context [term_occur _ _] |- _ ] => rewrite  term_occur_FOL_LAM in H
  | [H: context [task_term_occur _  _] |- _ ] => rewrite  task_term_occur_FOL_LAM in H
  | [H: context [pred_task_term_occur _  _] |- _ ] => rewrite pred_task_term_occur_FOL_LAM in H
  | [H: context [st_FOL2LAM (reducev _ _)] |- _ ] => rewrite reducev_FOL_LAM in H
  | [H: context [st_FOL2LAM (reducer _ _)] |- _ ] => rewrite reducer_FOL_LAM in H
  | [H: context [newv _] |- _] => rewrite newv_FOL_LAM in H
  | [H: context [newr _] |- _] => rewrite newr_FOL_LAM in H
(*   | [H: context [variable_list  (_++_)] |- _ ] => rewrite variable_list_app in H
  | [H: context [predname_list  (_++_)] |- _ ] => rewrite predname_list_app in H *)
  | [H: context [prop_ustr _] |- _ ] => rewrite prop_ustr_FOL_LAM in H
  | [H: context [term_ustr _ ] |- _ ] => rewrite  term_ustr_FOL_LAM in H
  | [H: context [task_ustr _] |- _ ] => rewrite task_ustr_FOL_LAM in H
  | [H: context [term2tm (term_sub _ _)] |- _ ] => rewrite term_sub_FOL_LAM in H
  | [H: context [prop2tm (prop_var_sub _ _)] |- _ ] => rewrite prop_var_sub_FOL_LAM in H
  | [H: @Permutation subst_task _ _ |- _ ] => apply subst_task_Permutation_FOL_LAM in H
  | [|- term_alpha_eq _ _ _ ] => rewrite term_alpha_eq_FOL_LAM 
  | [|- alpha_eq _ _ _]=> rewrite alpha_eq_FOL_LAM 
  | [|- aeq _ _ ] => rewrite aeq_FOL_LAM 
  | [|- context [update _ _  _ ] ] => rewrite  update_FOL_LAM 
  | [|- context [free_occur _ _] ] => rewrite  free_occur_FOL_LAM 
  | [|- context [pred_free_occur _ _] ] => rewrite  pred_free_occur_FOL_LAM 
  | [|- context [term_occur _ _] ] => rewrite  term_occur_FOL_LAM 
  | [|- context [task_term_occur _  _] ] => rewrite  task_term_occur_FOL_LAM 
  | [|- context [pred_task_term_occur _  _] ] => rewrite pred_task_term_occur_FOL_LAM 
  | [|- context [st_FOL2LAM (reducev _ _)] ] => rewrite  reducev_FOL_LAM
  | [|- context [st_FOL2LAM (reducer _ _)] ] => rewrite  reducer_FOL_LAM
  | [|- context [newv _] ] => rewrite newv_FOL_LAM
  | [|- context [newr _] ] => rewrite newr_FOL_LAM
(*   | [|- context [variable_list  (_++_)] ] => rewrite variable_list_app 
  | [|- context [predname_list  (_++_)] ] => rewrite predname_list_app  *)
  | [|- context [prop_ustr _]  ] => rewrite prop_ustr_FOL_LAM
  | [|- context [term_ustr _]  ] => rewrite  term_ustr_FOL_LAM
  | [|- context [task_ustr _] ] => rewrite task_ustr_FOL_LAM
  | [|- context [term2tm (term_sub _ _)]  ] => rewrite term_sub_FOL_LAM 
  | [|- context [prop2tm (prop_var_sub _ _)] ] => rewrite prop_var_sub_FOL_LAM
  end.

End DemoSugarLambda.