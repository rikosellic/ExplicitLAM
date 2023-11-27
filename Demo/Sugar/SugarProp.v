Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Relation_Operators.
Require Import Permutation.
Require Import RelationClasses.
Require Import Morphisms.
Require Import FV.Demo.Sugar.SugarLambda.
Require Import FV.utils.
Require Import FV.Demo.Lambda.
Import ListNotations.

Module DemoSugar.

Include DemoSugarLambda.

Open Scope Sugar_scope.

Tactic Notation "cname" := destruct_name.

Tactic Notation "FOL2LAM" := FOL2LAM.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*** Basic definitions and lemmas ***)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Lemma vars_new_xs_length: forall xs P st,
  length (vars_new_xs P xs st) = length xs.
Proof.  
    induction xs; intros. easy. simpl. 
    destruct (task_term_occur a (reducev a st)); simpl; auto.
Qed.

Lemma in_preds_dec: forall (r: R.t) rs,
 {In r rs} + {~ In r rs}.
Proof.
  induction rs.
  + now right.
  + destruct (R.eq_dec a r).
     - left. now left. 
     - destruct IHrs. left. now right. 
        right. apply not_in_cons. split. congruence. easy. 
Qed.


Lemma task_ustr_app: forall st1 st2,
  task_ustr (st1++st2) = task_ustr st1 ++ task_ustr st2.
Proof. intros. apply flat_map_app. Qed.

Lemma pred_task_term_occur_app: forall r st1 st2,
  pred_task_term_occur r (st1++st2) = pred_task_term_occur r st1 + pred_task_term_occur r st2.
Proof. induction st1; intros. easy. destruct a; simpl; cname; rewrite IHst1; apply PeanoNat.Nat.add_assoc. Qed.

Lemma task_term_occur_app: forall x st1 st2,
  task_term_occur x (st1++st2) = task_term_occur x st1 + task_term_occur x st2.
Proof.  induction st1; intros. easy. destruct a; simpl; cname; rewrite IHst1; apply PeanoNat.Nat.add_assoc. Qed.

Lemma newv_list_new_name: forall xs,
  V.list_new_name xs = newv (map uvar xs).
Proof.
  destruct xs.
  + easy.
  + simpl. unfold newv. simpl. now rewrite variable_list_map_uvar.
Qed. 

Lemma no_pred_occur_no_pred_free_occur: forall r P,
  pred_occur r P = 0 ->
  pred_free_occur r P =0.
Proof. induction P; intros; simpl; simpl in H; zero_r H; try rewrite IHP1; try rewrite IHP2; try congruence; try tauto; cname. Qed.

Lemma not_in_predname_list_no_pred_occur: forall r P,
  ~ In r (predname_list (prop_ustr P)) -> pred_occur r P = 0.
Proof.
  induction P; intros; simpl in *; try congruence; try rewrite predname_list_app in H; try des_notin H; 
  try rewrite IHP; try rewrite IHP1; try rewrite IHP2; try easy.
  + induction a.
      - simpl in H. des_notin H. cname.
      - simpl in H. rewrite predname_list_app in H. des_notin H. tauto.
  + cname.
  + rewrite predname_list_app in H1. now des_notin H1.
Qed.   

Lemma not_in_predname_list_no_pred_task_term_occur: forall r st,
  ~ In r (predname_list (task_ustr st)) -> pred_task_term_occur r st = 0.
Proof.
  induction st; intros. easy. simpl in H. rewrite predname_list_app in H. des_notin H. destruct a.
  + tauto. 
  + simpl in H. des_notin H. des_notin H1. cname.
  + des_notin H. rewrite predname_list_app in H1. des_notin H1. simpl. 
      rewrite no_pred_occur_no_pred_free_occur. now rewrite IHst.
      now apply not_in_predname_list_no_pred_occur.
Qed.   

Lemma newr_valid: forall l,
  ~ In (newr l) (predname_list l).
Proof. 
  intros. unfold newr. unfold new_ustr. apply not_in_forall. 
  rewrite Forall_forall. pose proof R.list_new_name_new.
  intros. apply H in H0. congruence.
Qed.

Fixpoint pred_domain (st: subst_task):=
  match st with
  | nil => nil
  | (spred r1 r2):: st0 => r1::(pred_domain st0)
  | (sprop r xs P):: st0 => r::(pred_domain st0)
  | _:: st0 => pred_domain st0
  end.

(** Lemmas about nil **)
Lemma term_sub_nil: forall t,
  term_sub nil t = t.
Proof.
  intros. add_some. repeat rewrite <- term2tm_tm2term.
  f_equal. FOL2LAM. now rewrite LAM.subst_nil. 
Qed.  

Corollary atom_var_sub_nil: forall a,
  atom_var_sub nil a = a.
Proof. induction a. easy. simpl. rewrite term_sub_nil. congruence. Qed.

Lemma atom_sub_aux_nil: forall a ts,
  atom_sub_aux a ts nil = PAtom (construct_atom a ts).  
Proof.
  intros. revert ts. induction a; intros.
  + easy.
  + simpl. rewrite term_sub_nil. rewrite  construct_atom_app. auto.
Qed.  

Corollary atom_sub_nil: forall a,
  atom_sub nil a = PAtom a.
Proof. intros. apply atom_sub_aux_nil. Qed.

Lemma vars_new_st_nil: forall d xs,
  vars_new_st d xs nil = nil.
Proof. now induction xs. Qed.

Lemma vars_new_xs_nil: forall d xs,
  vars_new_xs d xs nil = xs.
Proof. induction xs. easy. simpl. congruence. Qed.

Lemma prop_var_sub_nil: forall p,
  prop_var_sub nil p = p.
Proof.
  intros. add_some. repeat rewrite <- prop2tm_tm2prop.
  f_equal. FOL2LAM. now rewrite LAM.subst_nil. constructor. 
Qed.

Lemma prop_sub_nil: forall p,
  prop_sub nil p = p.
Proof.
  induction p; simpl; try repeat rewrite term_sub_nil; try rewrite atom_sub_nil; try congruence.
  rewrite vars_new_xs_nil. rewrite vars_new_st_nil. congruence.
Qed.

Lemma term_ustr_predname_list: forall t,
  predname_list (term_ustr t) = nil.
Proof.  induction t; simpl; try rewrite predname_list_app; try congruence; now rewrite IHt1. Qed.

(** Lemmas about reduce **)
Definition no_var_sub(st:subst_pair):=
  match st with
  | svar _ _ => False
  | _ => True
  end.

Definition get_var_sub (st:subst_task):=
  filter (fun p => match p with | svar _ _ => true | _ => false end) st.
  
Definition get_pred_sub (st:subst_task):=
  filter (fun p => match p with | svar _ _ => false | _ => true end) st.

Lemma reducev_app: forall x l1 l2,
  reducev x (l1++l2) = reducev x l1 ++ reducev x l2.
Proof. intros. apply filter_app. Qed.

Lemma reducer_app: forall x l1 l2,
  reducer x (l1++l2) = reducer x l1 ++ reducer x l2.
Proof. intros. apply filter_app. Qed. 

Lemma reducev_no_var_sub: forall x st,
  Forall no_var_sub st ->
  reducev x st = st.
Proof.
  induction st; intros. easy. destruct a; forall_cons H.
  - inversion H.
  - simpl. now rewrite IHst.  
  - simpl. now rewrite IHst.
Qed.

Lemma reducer_no_var_sub: forall r st,
  Forall no_var_sub st ->
  Forall no_var_sub (reducer r st).
Proof.
  induction st; intros.
  + constructor.
  + forall_cons H. destruct a. inversion H. 
      cname. apply Forall_cons. constructor. tauto. 
      cname. apply Forall_cons. constructor. tauto.
Qed.

Lemma reducev_swap: forall x y st,
  reducev x (reducev y st) =  reducev y (reducev x st).
Proof. induction st. easy. destruct a; repeat cname. Qed.

Lemma reducer_swap: forall x y st,
  reducer x (reducer y st) =  reducer y (reducer x st).
Proof. induction st. easy. destruct a; repeat cname. Qed.

Lemma reducev_reducer_swap: forall x r st,
  reducev x (reducer r st) = reducer r (reducev x st).
Proof. induction st. easy. destruct a; repeat cname. Qed.

Lemma reducer_reducer: forall r st,
  reducer r (reducer r st) = reducer r st.
Proof. induction st. easy. destruct a; repeat cname. Qed.

Lemma reducev_reducev: forall x st,
  reducev x (reducev x st) = reducev x st.
Proof. induction st. easy. destruct a; repeat cname. Qed.

Lemma reducev_no_task_term_occur: forall x x0 st,
  task_term_occur x st = 0 ->
  task_term_occur x (reducev x0 st) = 0.
Proof. intros. FOL2LAM. now apply LAM.reduce_no_st_tm_occur. Qed.

Lemma reducer_no_task_term_occur: forall r x st,
  task_term_occur x st = 0 ->
  task_term_occur x (reducer r st) = 0.
Proof. intros. FOL2LAM. now apply LAM.reduce_no_st_tm_occur. Qed.

Lemma reducer_no_pred_task_term_occur: forall r r0 st,
  pred_task_term_occur r st = 0 ->
  pred_task_term_occur r (reducer r0 st) = 0.
Proof. intros. FOL2LAM. now apply LAM.reduce_no_st_tm_occur. Qed.

Lemma reducev_pred_task_term_occur: forall r x st,
  pred_task_term_occur r (reducev x st) =  pred_task_term_occur r st .
Proof. induction st. easy. destruct a; cname. Qed.

Lemma get_var_sub_app: forall st1 st2,
  get_var_sub (st1++st2) = get_var_sub st1 ++ get_var_sub st2.
Proof. intros. apply filter_app. Qed. 

Lemma get_pred_sub_app: forall st1 st2,
  get_pred_sub (st1++st2) = get_pred_sub st1 ++ get_pred_sub st2.
Proof. intros. apply filter_app. Qed. 
  
Lemma get_var_sub_only_var_sub: forall st,
  Forall only_var_sub (get_var_sub st).
Proof. induction st. constructor. destruct a; simpl; now repeat constructor. Qed.

Lemma get_pred_sub_no_var_sub: forall st,
  Forall no_var_sub (get_pred_sub st).
Proof. induction st. constructor. destruct a; simpl; now repeat constructor. Qed.

Lemma only_var_sub_get_var_sub: forall st,
  Forall only_var_sub st ->
  get_var_sub st = st.
Proof. induction st. easy. intros. destruct a; forall_cons H; try inversion H; subst. simpl. now rewrite IHst. Qed.

Lemma no_var_sub_get_var_sub: forall st,
  Forall no_var_sub st ->
  get_var_sub st = nil.
Proof. induction st. easy. intros. destruct a; forall_cons H; try inversion H; subst. simpl. now rewrite IHst. simpl. now rewrite IHst. Qed.

Lemma no_var_sub_get_pred_sub: forall st,
  Forall no_var_sub st ->
  get_pred_sub st = st.
Proof. induction st. easy. intros. destruct a; forall_cons H; try inversion H; subst. simpl. now rewrite IHst. simpl. now rewrite IHst.  Qed.

Lemma only_var_sub_get_pred_sub: forall st,
  Forall only_var_sub st ->
  get_pred_sub st = nil.
Proof. induction st. easy. intros. destruct a; forall_cons H; try inversion H; subst. simpl. now rewrite IHst.  Qed.

Lemma get_var_sub_reducev_swap: forall x st,
  get_var_sub (reducev x st) = reducev x (get_var_sub st).
Proof. induction st. easy. destruct a; cname. simpl. congruence. Qed.

Lemma get_pred_sub_reducev_swap: forall x st,
  get_pred_sub (reducev x st) = reducev x (get_pred_sub st).
Proof. induction st. easy. destruct a; cname. Qed.

Lemma get_var_sub_reducer_swap: forall x st,
  get_var_sub (reducer x st) = reducer x (get_var_sub st).
Proof. induction st. easy. destruct a; cname.  Qed.

Lemma get_pred_sub_reducer_swap: forall x st,
  get_pred_sub (reducer x st) = reducer x (get_pred_sub st).
Proof. induction st. easy. destruct a; cname; simpl; congruence. Qed.

Lemma get_pred_sub_reducev: forall x st,
  get_pred_sub (reducev x st) = get_pred_sub st.
Proof. intros. rewrite get_pred_sub_reducev_swap. rewrite reducev_no_var_sub. easy. apply get_pred_sub_no_var_sub. Qed.

Lemma vars_new_st_get_pred_sub: forall P xs st,
  get_pred_sub (vars_new_st P xs st) = get_pred_sub st.
Proof.
  induction xs; intros. easy.
  simpl. destruct (task_term_occur a (reducev a st)); 
  rewrite IHxs; simpl; now rewrite get_pred_sub_reducev.
Qed.

Lemma pred_task_term_occur_get_pred_sub: forall r st,
  pred_task_term_occur r (get_pred_sub st) = pred_task_term_occur r st.
Proof. induction st. easy. destruct a; simpl; cname. Qed.

Lemma vars_new_st_pred_task_term_occur: forall r P xs st,
  pred_task_term_occur r (vars_new_st P xs st) = pred_task_term_occur r st.
Proof.  
  induction xs; intros. easy.
  simpl. destruct (task_term_occur a (reducev a st)); simpl; rewrite IHxs; simpl;
  now rewrite reducev_pred_task_term_occur. 
Qed.

Lemma get_pred_sub_predname_list: forall st,
  predname_list (task_ustr (get_pred_sub st)) = predname_list (task_ustr st).
Proof.
  induction st. easy.
  destruct a; simpl.
  + rewrite predname_list_app. now rewrite term_ustr_predname_list.
  + now do 2 f_equal.
  + f_equal. repeat rewrite predname_list_app. now rewrite IHst. 
Qed.

Corollary newr_get_pred_sub: forall st,
  newr (task_ustr (get_pred_sub st)) = newr (task_ustr st).
Proof. intros. repeat rewrite newr_FOL_LAM. f_equal. apply get_pred_sub_predname_list. Qed.

Lemma reducev_pred_domain: forall x st,
  pred_domain (reducev x st) = pred_domain st.
Proof. induction st. easy. destruct a; simpl; try congruence. cname. Qed.

Lemma not_in_reducer_self_pred_domian: forall r st,
  ~ In r (pred_domain (reducer r st)).
Proof. induction st. easy. destruct a; simpl; cname; simpl; apply not_in_cons; tauto. Qed.  

Lemma vars_new_st_pred_domain: forall P xs st,
  pred_domain (vars_new_st P xs st) = pred_domain st.
Proof. 
  intros. revert P st. induction xs; intros. easy. 
  simpl. destruct ( task_term_occur a (reducev a st) ); 
  rewrite IHxs; simpl; apply reducev_pred_domain.
Qed.

Lemma in_pred_domain_reducer_other_iff: forall r r0 st,
  r <> r0 ->
  (In r (pred_domain st) <-> In r (pred_domain (reducer r0 st))).
Proof.
  induction st; intros.
  + split; intros; inversion H0.
  + destruct a. 
      - tauto.
      - split; intros; simpl in *. 
        * destruct H0.
            ++ subst r1. cname. now left.
            ++ cname. right. tauto.
        * cname. destruct H0; tauto.
      - split; intros; simpl in *. 
         * destruct H0.
            ++ subst r1. cname. now left.
            ++ cname. right. tauto.
         * cname. destruct H0; tauto.
Qed.

Lemma not_in_pred_domain_reducer_other_iff: forall r r0 st,
  r <> r0 ->
  ( ~ In r (pred_domain st) <-> ~ In r (pred_domain (reducer r0 st))).
Proof.
  induction st; intros.
  + split; intros; easy.
  + destruct a. 
      - tauto.
      - split; intros; simpl in *. 
        * cname. simpl. des_notin H0. tauto. 
        * cname; apply not_in_cons.  tauto. des_notin H0. split. congruence. tauto. 
      - split; intros; simpl in *. 
         * cname. simpl. tauto.  
         * cname; apply not_in_cons. tauto. des_notin H0. split. congruence. tauto.
Qed.


(**  Lemmas about Permutation **)
Lemma newv_Permutation: forall l1 l2,
  Permutation l1 l2 ->
  newv l1 = newv l2.
Proof.  
  intros. repeat rewrite newv_FOL_LAM. apply V.list_new_name_Permutation.
  now apply variable_list_Permutation.
Qed.

Lemma newr_Permutation: forall l1 l2,
  Permutation l1 l2 ->
  newr l1 = newr l2.
Proof.  
  intros. repeat rewrite newr_FOL_LAM. apply R.list_new_name_Permutation.
  now apply predname_list_Permutation.
Qed.

Lemma task_ustr_Permutation: forall st1 st2,
  Permutation st1 st2 ->
  Permutation (task_ustr st1) (task_ustr st2).
Proof.
  intros. induction H.
  + constructor.
  + destruct x; simpl;perm.
  +  destruct x; destruct y; simpl; perm.
      - pose proof Permutation_app_comm_tail ustr (upred r :: upred r0::nil) (uvar x::term_ustr t). 
        apply H. perm.
      - pose proof Permutation_app_comm_tail ustr  (uvar x::term_ustr t) (upred r :: upred r0::nil)(task_ustr l)(task_ustr l).
         simpl in H. apply H. perm.
      - pose proof Permutation_app_comm_tail ustr  (upred r1::upred r2::nil) (upred r:: upred r0::nil). apply H. perm.
      - pose proof Permutation_app_comm_tail ustr (upred r::upred r0::nil)(upred r1 :: map uvar xs ++prop_ustr P)(task_ustr l)(task_ustr l).
         simpl in H.  repeat rewrite <- app_assoc in H. repeat rewrite <- app_assoc. symmetry.  apply H. perm. 
      - pose proof Permutation_app_comm_tail ustr (upred r :: map uvar xs ++prop_ustr P) (upred r0::upred r1::nil) 
        (task_ustr l) (task_ustr l). simpl in H.   repeat rewrite <- app_assoc in H.  repeat rewrite <- app_assoc. symmetry. apply H. perm.
  + perm.
Qed.  

Lemma reducev_Permutation: forall x st1 st2,
  Permutation st1 st2 ->
  Permutation (reducev x st1) (reducev x st2).
Proof.
  intros. induction H. easy.
  + destruct x0; simpl; cname; now constructor.
  + destruct x0; destruct y; cname; try now constructor. apply Permutation_refl.
  + econstructor; eauto.
Qed. 

Lemma reducer_Permutation: forall x st1 st2,
  Permutation st1 st2 ->
  Permutation (reducer x st1) (reducer x st2).
Proof.
  intros. induction H. easy.
  + destruct x0; simpl; cname; now constructor.
  + destruct x0; destruct y; cname; try now constructor. apply Permutation_refl.
      apply Permutation_refl. apply Permutation_refl. apply Permutation_refl. 
  + econstructor; eauto.
Qed. 

Lemma task_term_occur_Permutation: forall x st1 st2,
  Permutation st1 st2 ->
  task_term_occur x st1 = task_term_occur x st2.
Proof. intros. FOL2LAM. apply subst_task_Permutation_FOL_LAM in H. now apply LAM.st_tm_occur_Permutation. Qed.

Lemma pred_task_term_occur_Permutation: forall x st1 st2,
  Permutation st1 st2 ->
  pred_task_term_occur x st1 = pred_task_term_occur x st2.
Proof. intros. FOL2LAM. apply subst_task_Permutation_FOL_LAM in H. now apply LAM.st_tm_occur_Permutation. Qed.

Lemma divide_subst_task_Permutation: forall st,
  Permutation st (get_var_sub st ++ get_pred_sub st).  
Proof.
  induction st; intros.
  + constructor. 
  + destruct a.
      - simpl. now constructor.
      - simpl. econstructor. 2: apply Permutation_middle. now constructor.
      - simpl. econstructor. 2: apply Permutation_middle. now constructor.
Qed.

Ltac nperm:=
  repeat match goal with
  | H: Permutation ?a ?b |- Permutation ?a ?b => apply H
  | |- newv _ = newv _ => apply newv_Permutation
  | |- newr _ = newr _ => apply newr_Permutation
  | |- task_term_occur ?x _ = task_term_occur ?x _ => apply task_term_occur_Permutation
  | |- pred_task_term_occur ?x _ = pred_task_term_occur ?x _ => apply pred_task_term_occur_Permutation
  | |- Permutation (task_ustr _) (task_ustr _) => apply task_ustr_Permutation
  | |- Permutation (reducev ?x _) (reducev ?x _) => apply reducev_Permutation
  | |- Permutation (reducer ?r _) (reducer ?r _) => apply reducer_Permutation
  | _ => perm
  end.

Lemma vars_new_xs_Permutation: forall xs P st1 st2,
  Permutation st1 st2 ->
  vars_new_xs P xs st1= vars_new_xs P xs st2.
Proof.
  induction xs; intros. easy. simpl.
  assert (task_term_occur a (reducev a st2)= task_term_occur a (reducev a st1)) by nperm. 
  rewrite H0. destruct H0. destruct (task_term_occur a (reducev a st2)).
  + f_equal. apply IHxs. now apply reducev_Permutation.
  + assert (newv (uvar a :: map uvar xs ++ prop_ustr P ++ task_ustr (reducev a st2))=
      newv (uvar a :: map uvar xs ++ prop_ustr P ++ task_ustr (reducev a st1))) by nperm.
      rewrite H0. clear H0. f_equal. apply IHxs. nperm.
Qed.

Lemma vars_new_st_Permutation: forall xs P st1 st2,
  Permutation st1 st2 ->
  Permutation (vars_new_st P xs st1) (vars_new_st P xs st2).
Proof.
  induction xs; intros. easy. 
  simpl. assert (task_term_occur a (reducev a st2)= task_term_occur a (reducev a st1)) by nperm.
  rewrite H0. clear H0. destruct (task_term_occur a (reducev a st1)). apply IHxs. nperm.
  apply IHxs. assert (newv (uvar a :: map uvar xs ++ prop_ustr P ++ task_ustr (reducev a st2))=
      newv (uvar a :: map uvar xs ++ prop_ustr P ++ task_ustr (reducev a st1))) by nperm.
  rewrite H0. nperm.
Qed.

(** Lemmas about substitution **)
Lemma term_sub_reducer: forall r t st,
  term_sub (reducer r st) t = term_sub st t.
Proof. 
  induction t; intros; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try congruence.
  induction st. easy. destruct a; cname.
Qed.

Lemma term_sub_no_var_sub: forall t st,
  Forall no_var_sub st ->
  term_sub st t = t.
Proof.
  induction t; intros; simpl in *;  try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try congruence.
  induction st. easy. forall_cons H. destruct a; try inversion H; tauto.
Qed.  

Lemma term_sub_get_var_sub: forall t st,
  term_sub (get_var_sub st) t = term_sub st t.
Proof.
  induction t; intros; simpl; try congruence.
  induction st. easy. destruct a; cname.
Qed.

(** Lemmas abot atom **)
(** Number of terms in the atom **)
Fixpoint atom_length(a:atom):nat:=
  match a with
  | APred _ => 0
  | AApp a0 _ => S (atom_length a0)
  end.
   
Fixpoint atom_terms(a:atom): list term:=
  match a with
  | APred _ => nil
  | AApp a0 t =>  atom_terms a0++[t]
  end.
  
Lemma atom_terms_length: forall a,
  length (atom_terms a) = atom_length a.
Proof. induction a; simpl; try easy. rewrite app_length. simpl. rewrite IHa. apply PeanoNat.Nat.add_1_r. Qed.
  
Lemma construct_atom_length: forall a ts,
   atom_length (construct_atom a ts) = atom_length a + length ts.
Proof.
  intros. revert a. induction ts; intros. easy. 
  simpl. rewrite IHts. simpl. apply plus_n_Sm.
Qed.

Lemma construct_atom_pred: forall a ts,
  atom_pred (construct_atom a ts) = atom_pred a.
Proof.  
  intros. revert a. induction ts; intros. easy.
  simpl. now rewrite IHts.
Qed. 

Lemma atom_var_sub_atom_pred: forall a st,
  atom_pred (atom_var_sub st a) = atom_pred a.
Proof. induction a; intros. easy. apply IHa. Qed.

Lemma atom_var_sub_length: forall a st,
  atom_length (atom_var_sub st a) = atom_length a.
Proof. induction a; intros. easy. simpl. f_equal. apply IHa. Qed. 

Lemma extend_pred_reducer_other: forall r r0 st ts,
  r <>r0 ->
  extend_pred r ts (reducer r0 st)  = extend_pred r ts st.
Proof.
  induction st; intros. easy.
  destruct a; simpl; auto.
  + cname. auto.  cname. cname. auto.
  + cname. auto. cname. cname. auto.
Qed.

Lemma atom_sub_aux_reducer_other: forall a r st ts,
  atom_pred a <> r ->
  atom_sub_aux a ts (reducer r st)   = atom_sub_aux a ts st .
Proof. 
  induction a; intros. simpl. apply extend_pred_reducer_other. easy. 
  simpl. rewrite term_sub_reducer. now apply IHa.
Qed.

Corollary atom_sub_reducer_other: forall a r st,
  atom_pred a <> r ->
  atom_sub  (reducer r st) a = atom_sub st a.
Proof. intros. now apply atom_sub_aux_reducer_other. Qed. 

Lemma atom_var_sub_get_var_sub: forall a st,
  atom_var_sub (get_var_sub st) a = atom_var_sub st a.
Proof. induction a; intros. easy. simpl.  rewrite IHa. now rewrite term_sub_get_var_sub. Qed.

Lemma extend_pred_get_pred_sub: forall r ts st,
  extend_pred r ts (get_pred_sub st) = extend_pred r ts st.
Proof. induction st. easy. destruct a; cname. Qed.

Local Ltac rew:=
  repeat match goal with
  | H: context [ length (vars_new_xs _ _ _) ] |- _ => rewrite vars_new_xs_length in H
  | H: context [ prop_var_sub nil _ ] |- _ => rewrite prop_var_sub_nil
  | H: context [ _++ nil] |- _ => rewrite <- app_nil_end in H
  | H: context [reducer ?r (reducer ?r _)] |- _ => rewrite reducer_reducer in H 
  | H: context [reducev ?x (reducev ?x _)] |- _ => rewrite reducev_reducev in H 
  | H: context [predname_list (task_ustr (get_pred_sub _))] |- _ => rewrite get_pred_sub_predname_list in H
  | H: context [get_pred_sub (vars_new_st _ _ _)] |- _=> rewrite vars_new_st_get_pred_sub in H
  | H: context [get_pred_sub (get_pred_sub _)] |- _ => rewrite no_var_sub_get_pred_sub in H; try apply get_pred_sub_no_var_sub
  | H: context [get_var_sub (get_var_sub _)] |- _ => rewrite only_var_sub_get_var_sub in H; try apply get_var_sub_only_var_sub
  | H: context [get_pred_sub (reducev _ _)] |- _ => rewrite get_pred_sub_reducev in H
  | H: context [reducev _ (get_pred_sub _)] |- _ => rewrite <- get_pred_sub_reducev_swap in H; rewrite get_pred_sub_reducev in H
  | H: context [pred_task_term_occur _ (reducev _ _)] |- _ => rewrite reducev_pred_task_term_occur in H
  | H: context [pred_task_term_occur _ (get_pred_sub _)] |- _ => rewrite pred_task_term_occur_get_pred_sub in H
  | H: context [pred_task_term_occur _ (vars_new_st _ _ _)] |- _ => rewrite vars_new_st_pred_task_term_occur in H
  | |- context [ length (vars_new_xs _ _ _) ] => rewrite vars_new_xs_length
  | |- context [ prop_var_sub nil _ ] => rewrite prop_var_sub_nil
  | |- context [ _++ nil] => rewrite <- app_nil_end 
  | |- context [reducer ?r (reducer ?r _)]  => rewrite reducer_reducer 
  | |- context [reducev ?x (reducev ?x _)]  => rewrite reducev_reducev 
  | |- context [ predname_list (task_ustr (get_pred_sub _))] => rewrite get_pred_sub_predname_list
  | |- context [get_pred_sub (vars_new_st _ _ _)] => rewrite vars_new_st_get_pred_sub
  | |- context [get_pred_sub (get_pred_sub _)] => rewrite no_var_sub_get_pred_sub ; try apply get_pred_sub_no_var_sub
  | |- context [get_var_sub (get_var_sub _)]  => rewrite only_var_sub_get_var_sub; try apply get_var_sub_only_var_sub
  | |- context [get_pred_sub (reducev _ _)] => rewrite get_pred_sub_reducev
  | |- context [reducev _ (get_pred_sub _)]  => rewrite <- get_pred_sub_reducev_swap; rewrite get_pred_sub_reducev
  | |- context [pred_task_term_occur _ (reducev _ _)]  => rewrite reducev_pred_task_term_occur
  | |- context [pred_task_term_occur _ (get_pred_sub _)]  => rewrite pred_task_term_occur_get_pred_sub 
  | |- context [pred_task_term_occur _ (vars_new_st _ _ _)] => rewrite vars_new_st_pred_task_term_occur
  | |- _ => try tauto
  end.

Ltac pred_notin:=
  try match goal with
  | |- pred_free_occur _ _ = 0 => apply no_pred_occur_no_pred_free_occur; 
                                                         apply not_in_predname_list_no_pred_occur
  | |- pred_occur  _ _ = 0 => apply not_in_predname_list_no_pred_occur
  | |- pred_task_term_occur _ _ = 0 => apply not_in_predname_list_no_pred_task_term_occur
  end;
  try match goal with    
  | H:?z = newr ?l |- ~ In ?z _ => rewrite H; pose proof (newr_valid l) 
  | H:?z = newr ?l |-  ?z <> _ => rewrite H; pose proof (newr_valid l) 
  | H:?z = newr ?l |- _ <> ?z => rewrite H; pose proof (newr_valid l) 
  | |- ~ In (newr ?l) _  => pose proof (newr_valid l) 
  | |- _ <> newr ?l => pose proof (newr_valid l) 
  | |-  newr ?l <> _ => pose proof (newr_valid l) 
  end;
  try repeat (simpl in * ;match goal with
  | H: ~ In _ (_::_) |- _  => des_notin H
  | H: ~ In _ (_++_) |- _  => des_notin H
  | H: ~ (_ \/ _) |- _ => des_notin H
  | H: context [predname_list (_ ++ _ )] |- _ => rewrite predname_list_app in H
  | H: context [reducer _ (_++_)] |- _ => rewrite reducer_app in H
  | H: context [reducev _ (_++_)] |- _ => rewrite reducev_app in H
  | H: context [task_ustr (_ ++ _)] |- _ => rewrite task_ustr_app in H
  | H: ?x <> ?x |- _ => congruence
  end );
   try repeat match goal with
  | |- context [predname_list (_ ++ _ )] => rewrite predname_list_app 
  | |- context [reducer _ (_++_)] => rewrite reducer_app 
  | |- context [reducev _ (_++_)] => rewrite reducev_app 
  | |- context [task_ustr (_ ++ _)]  => rewrite task_ustr_app
  | |- ~ (_\/_) => apply deMorgan2; split
  | |- ~ In _ (_::_) => apply not_in_cons; split
  | |- ~ In _ (_++_)  => apply not_in_app; split
  | |- ~ In _ _  => tauto
  | _ => try congruence; tauto
 end.

(**  Subst task equivalence **)
Definition st_eqv (st1 st2: subst_task):=
  get_var_sub st1 = get_var_sub st2 /\ get_pred_sub st1 = get_pred_sub st2.

Lemma term_sub_st_eqv: forall t st1 st2,
  st_eqv st1 st2 ->
  term_sub st1 t = term_sub st2 t.
Proof. 
      intros. rewrite  <- term_sub_get_var_sub. 
      rewrite  <- term_sub_get_var_sub with (st:=st2).
      destruct H. congruence.
Qed.

Lemma divide_subst_task_st_eqv: forall st,
  st_eqv st (get_var_sub st ++ get_pred_sub st).
Proof. 
  intros. unfold st_eqv. rewrite get_var_sub_app. rewrite get_pred_sub_app. split.
 + assert (get_var_sub (get_var_sub st) = get_var_sub st). rewrite only_var_sub_get_var_sub.
     easy. apply get_var_sub_only_var_sub.
     assert (get_var_sub (get_pred_sub st) = nil).
     apply no_var_sub_get_var_sub. apply get_pred_sub_no_var_sub. 
     rewrite H. rewrite H0. apply app_nil_end.
 + assert (get_pred_sub (get_var_sub st) = nil). apply only_var_sub_get_pred_sub.
     apply get_var_sub_only_var_sub. rewrite H. clear H. simpl.
     assert (get_pred_sub (get_pred_sub st)=get_pred_sub st).
     rewrite no_var_sub_get_pred_sub. easy. apply get_pred_sub_no_var_sub. congruence.
Qed.

Corollary st_eqv_Permutation: forall st1 st2,
  st_eqv st1 st2 ->
  Permutation st1 st2.
Proof.
  intros. destruct H. econstructor. apply divide_subst_task_Permutation. econstructor.
  2:{ apply Permutation_sym. apply divide_subst_task_Permutation. } rewrite H. rewrite H0.
  apply Permutation_refl.
Qed.

Fact st_eqv_refl: Reflexive st_eqv.
Proof. unfold Reflexive. intros. unfold st_eqv. easy. Qed. 

Fact st_eqv_trans: Transitive st_eqv.
Proof. unfold Transitive. intros. destruct H. destruct H0. unfold st_eqv. split; congruence. Qed.

Fact st_eqv_sym: Symmetric st_eqv.
Proof. unfold Symmetric. intros. destruct H. unfold st_eqv. split; congruence. Qed.

Add Relation subst_task st_eqv reflexivity proved by st_eqv_refl symmetry proved by st_eqv_sym 
        transitivity proved by st_eqv_trans as st_eqv_equivalence.

Lemma st_eqv_task_term_occur: forall x st1 st2,
  st_eqv st1 st2 -> task_term_occur x st1 = task_term_occur x st2.
Proof. intros. apply task_term_occur_Permutation. now apply st_eqv_Permutation. Qed. 

Lemma st_eqv_pred_task_term_occur: forall x st1 st2,
  st_eqv st1 st2 -> pred_task_term_occur x st1 = pred_task_term_occur x st2.
Proof. intros. apply pred_task_term_occur_Permutation. now apply st_eqv_Permutation. Qed. 

Lemma reducev_st_eqv: forall x st1 st2,
  st_eqv st1 st2 ->
  st_eqv (reducev x st1) (reducev x st2).
Proof.
  intros. destruct H. unfold st_eqv. rewrite 2 get_var_sub_reducev_swap.
  rewrite 2 get_pred_sub_reducev_swap. split; congruence. Qed.

Lemma reducer_st_eqv: forall x st1 st2,
  st_eqv st1 st2 ->
  st_eqv (reducer x st1) (reducer x st2).
Proof.
  intros. destruct H. unfold st_eqv. rewrite 2 get_var_sub_reducer_swap.
  rewrite 2 get_pred_sub_reducer_swap. split; congruence. Qed.

Lemma st_eqv_cons: forall x st1 st2,
  st_eqv (x::st1) (x::st2) <-> st_eqv st1 st2.
Proof.
  split; intros.
  + destruct H. simpl in*. destruct x; try injection H as H; unfold st_eqv;split; congruence.
  + unfold st_eqv. destruct H. destruct x; simpl;split; congruence.
Qed.

Lemma vars_new_st_st_eqv: forall xs P st1 st2,
  st_eqv st1 st2 ->
  st_eqv (vars_new_st P xs st1) (vars_new_st P xs st2).
Proof.
  induction xs; intros. easy.
  simpl. assert (task_term_occur a (reducev a st2)=task_term_occur a (reducev a st1)).
  nperm. now apply st_eqv_Permutation. 
  rewrite H0. clear H0. destruct (task_term_occur a (reducev a st1)).
  + apply IHxs. now apply reducev_st_eqv.
  + assert (newv (uvar a :: map uvar xs ++ prop_ustr P ++ task_ustr (reducev a st1)) =
      newv (uvar a :: map uvar xs ++ prop_ustr P ++ task_ustr (reducev a st2))).
      nperm. now apply st_eqv_Permutation.
      rewrite H0. clear H0. apply IHxs. apply st_eqv_cons. now apply reducev_st_eqv.
Qed.

Lemma prop_var_sub_st_eqv: forall P st1 st2,
  st_eqv st1 st2 ->
  prop_var_sub st1 P = prop_var_sub st2 P.
Proof.
  induction P; intros; simpl; try congruence; try f_equal; auto; try now apply term_sub_st_eqv.
  + rewrite <- atom_var_sub_get_var_sub.  rewrite <- atom_var_sub_get_var_sub with (st:=st2).
      destruct H. congruence.
  + assert (task_term_occur x (reducev x st1) = task_term_occur x (reducev x st2)).
      nperm. now apply st_eqv_Permutation.
      rewrite H0. clear H0.  destruct (task_term_occur x (reducev x st2)).
      -  f_equal. apply IHP. now apply reducev_st_eqv.
      - assert (newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st1)) = newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st2))).
        nperm. now apply st_eqv_Permutation. rewrite H0. clear H0. f_equal. apply IHP. apply st_eqv_cons. now apply reducev_st_eqv. 
   + assert (task_term_occur x (reducev x st1) = task_term_occur x (reducev x st2)).
       nperm. now apply st_eqv_Permutation. rewrite H0. clear H0.  destruct (task_term_occur x (reducev x st2)).
      -  f_equal. apply IHP. now apply reducev_st_eqv.
      - assert (newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st1)) = newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st2))).
         nperm. now apply st_eqv_Permutation. rewrite H0. clear H0. f_equal. apply IHP. apply st_eqv_cons. now apply reducev_st_eqv.     
   + apply vars_new_xs_Permutation. nperm. now apply st_eqv_Permutation.
   + apply IHP1. now apply vars_new_st_st_eqv.
Qed.

Lemma extend_pred_st_eqv: forall r ts st1 st2,
  st_eqv st1 st2 ->
  extend_pred r ts st1 = extend_pred r ts st2.
Proof.
  intros. destruct H.  rewrite <- extend_pred_get_pred_sub. 
  rewrite <- extend_pred_get_pred_sub with (st:=st2). congruence. 
Qed.

Lemma atom_sub_aux_st_eqv: forall a ts st1 st2,
  st_eqv st1 st2 ->
  atom_sub_aux a ts st1 = atom_sub_aux a ts st2.
Proof.
  induction a; intros. simpl. now apply extend_pred_st_eqv.
  simpl. assert (term_sub st1 t = term_sub st2 t) by now apply term_sub_st_eqv.
  rewrite H0. now apply IHa.
Qed.

Corollary atom_sub_st_eqv: forall a st1 st2,
  st_eqv st1 st2 ->
  atom_sub st1 a = atom_sub st2 a.
Proof. intros. now apply atom_sub_aux_st_eqv. Qed.

Lemma prop_sub_st_eqv: forall P st1 st2,
  st_eqv st1 st2 ->
  prop_sub st1 P = prop_sub st2 P.
Proof.
  induction P; intros; simpl; try congruence.
  + erewrite term_sub_st_eqv. 2: apply H.  erewrite term_sub_st_eqv with (t:=t2). 2: apply H. easy. 
  + erewrite term_sub_st_eqv. 2: apply H.  erewrite term_sub_st_eqv with (t:=t2). 2: apply H. easy. 
  + now apply atom_sub_aux_st_eqv.
  + f_equal; auto.
  + f_equal; auto.
  + f_equal; auto.
  + f_equal; auto.
  + f_equal; auto.
  + assert (task_term_occur x (reducev x st2)=task_term_occur x (reducev x st1)). nperm. now apply st_eqv_Permutation.
     rewrite H0. destruct (task_term_occur x (reducev x st1)). clear H0. f_equal. 
     apply IHP. now apply reducev_st_eqv.
     assert (newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st1))=newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st2))).
    nperm. now apply st_eqv_Permutation. rewrite H1.  clear H1. f_equal. apply IHP. apply st_eqv_cons. now apply reducev_st_eqv.
   + assert (task_term_occur x (reducev x st2)=task_term_occur x (reducev x st1)). nperm. now apply st_eqv_Permutation.
      rewrite H0. destruct (task_term_occur x (reducev x st1)). clear H0. f_equal. 
      apply IHP. now apply reducev_st_eqv.
      assert (newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st1))=newv (uvar x :: prop_ustr P ++ task_ustr (reducev x st2))).
      nperm. now apply st_eqv_Permutation. rewrite H1.  clear H1. f_equal. apply IHP. apply st_eqv_cons. now apply reducev_st_eqv.
    + assert (pred_task_term_occur r (reducer r st2)=pred_task_term_occur r (reducer r st1)). nperm. now apply st_eqv_Permutation.
      rewrite H0. destruct (pred_task_term_occur r (reducer r st1)). 
      - f_equal. 
         * apply vars_new_xs_Permutation. nperm. now apply st_eqv_Permutation. 
         * apply IHP1. now apply vars_new_st_st_eqv.
         * apply IHP2. now apply reducer_st_eqv.
     - assert (newr (upred r :: prop_ustr P2 ++ task_ustr (reducer r st1))=newr (upred r :: prop_ustr P2 ++ task_ustr (reducer r st2))).
        nperm. now apply st_eqv_Permutation. rewrite H1. clear H1. f_equal.
         * apply vars_new_xs_Permutation. nperm. now apply st_eqv_Permutation. 
         * apply IHP1. now apply vars_new_st_st_eqv.
         * apply IHP2. apply st_eqv_cons. now apply reducer_st_eqv.
Qed.


(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*      Closed                                            *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

(**  Closed: no free predicates**)
Definition closed (P:prop): Prop:= forall r, pred_free_occur r P = 0.

(*                                                                   *)
(*  Lemmas about closed                                 *)
(*                                                                   *)

Lemma prop_var_sub_keep_no_pred_free_occur: forall r P st,
  pred_free_occur r P = 0 ->
  pred_free_occur r (prop_var_sub st P) = 0.
Proof.
  intros r P. revert r. induction P; intros; simpl; simpl in H; zero_r H; [try rewrite IHP;
  try rewrite IHP1; try rewrite IHP2; auto..| idtac].
  +  revert r st H. induction a; intros.
        - simpl in *. cname.
        - simpl in *. now apply IHa.
  + destruct (task_term_occur x (reducev x st)); simpl; apply IHP; simpl; rew.
  + destruct (task_term_occur x (reducev x st)); simpl; apply IHP; simpl; rew.
  + cname. now rewrite IHP1. rewrite IHP1; try rewrite IHP2; easy. 
Qed.

Corollary instantiate_var_binder_keep_no_pred_free_occur: forall r P xs ts,
  pred_free_occur r P = 0 ->
  pred_free_occur r (instantiate_var_binder P xs ts) = 0.
Proof.
  intros. revert r P xs H. induction ts; destruct xs; intros; try easy.
  simpl. apply IHts. apply prop_var_sub_keep_no_pred_free_occur; rew. 
Qed. 

Lemma not_atom_pred_no_pred_atom_occur: forall r a,
  r <> atom_pred a ->
  pred_atom_occur r a = 0.
Proof.
  induction a; intros.
  + simpl in *. cname.
  + tauto.
Qed.   
  
Lemma extend_pred_keep_no_pred_free_occur: forall r r0 ts st,
  r <> r0 ->
  pred_task_term_occur r st = O ->
  pred_free_occur r (extend_pred r0 ts st) = O.
Proof.
  intros. revert r r0 ts H H0. induction st; intros.
  + simpl. apply not_atom_pred_no_pred_atom_occur. now rewrite construct_atom_pred.
  + destruct a; simpl in *.
      - now apply IHst.
      - zero_r H0. unfold pred_pred_occur in H0. cname. apply not_atom_pred_no_pred_atom_occur. 
         now rewrite construct_atom_pred. now apply IHst.
     - zero_r H0. cname.
        * now apply instantiate_var_binder_keep_no_pred_free_occur.
        * now apply IHst.
Qed.

Lemma atom_sub_aux_keep_no_pred_free_occur: forall r a ts st,
  pred_task_term_occur r st = 0 ->
  pred_atom_occur r a = 0 ->
  pred_free_occur r (atom_sub_aux a ts st) = 0.
Proof.
  induction a; intros.
  + simpl in *. cname. now apply extend_pred_keep_no_pred_free_occur.
  + simpl. now apply IHa.
Qed.  

Lemma prop_sub_keep_no_pred_free_occur: forall r P st,
  pred_task_term_occur r st = 0 ->
  pred_free_occur r P = 0 ->
  pred_free_occur r (prop_sub st P) = 0.
Proof.
  induction P; intros; simpl in *; zero_r H0; try rewrite IHP; try rewrite IHP1; try rewrite IHP2; auto.
  + now apply atom_sub_aux_keep_no_pred_free_occur.
  + destruct ( task_term_occur x (reducev x st)); simpl; apply IHP; simpl; rew.
  + destruct ( task_term_occur x (reducev x st)); simpl; apply IHP; simpl; rew.
  + destruct (pred_task_term_occur r0 (reducer r0 st)) eqn: E.
      - simpl. rewrite IHP1; rew. 
        cname. rewrite IHP2; rew. now apply reducer_no_pred_task_term_occur. 
      - simpl. rewrite IHP1; rew. simpl.
        cname.
        * apply reducer_no_pred_task_term_occur with (r:=r0) (r0:=r0) in H. rewrite H in E. discriminate.
        * apply IHP2. simpl. unfold pred_occur. cname. now rewrite reducer_no_pred_task_term_occur. easy.
Qed.

Lemma extend_pred_pred_not_free_occur_if_substed: forall r r0 ts st,
 pred_task_term_occur r st = 0 ->
 In r (pred_domain st) ->
 pred_free_occur r (extend_pred r0 ts st) = 0.
Proof.
  intros. revert r r0 ts H H0. induction st; intros.
  + easy.
  + destruct a.
      - simpl. now apply IHst. 
      - simpl. simpl in H0. destruct H0.
        * subst r1. cname.
            ++ simpl in H. zero_r H. cname.
                   apply not_atom_pred_no_pred_atom_occur. now rewrite construct_atom_pred.
            ++ apply extend_pred_keep_no_pred_free_occur. congruence.
                   simpl in H. cname. inversion H.
        * simpl in H.  cname. inversion H. inversion H.
           apply not_atom_pred_no_pred_atom_occur. now rewrite construct_atom_pred.
          now apply IHst.
      - simpl. simpl in H. zero_r H. simpl in H0. destruct H0.
          * subst r1. cname.
             ++ now apply instantiate_var_binder_keep_no_pred_free_occur.
             ++ apply extend_pred_keep_no_pred_free_occur. congruence. easy.
          * cname. now apply instantiate_var_binder_keep_no_pred_free_occur.
             now apply IHst.
Qed.
              
Lemma atom_sub_aux_pred_not_free_occur_if_substed: forall r a ts st,
  pred_task_term_occur r st = 0 ->
  In r (pred_domain st) ->
  pred_free_occur r (atom_sub_aux a ts st) = 0.
Proof.
  induction a; intros.
  + now apply extend_pred_pred_not_free_occur_if_substed.
  + simpl. now apply IHa.
Qed.
  
Lemma pred_not_free_occur_if_substed: forall r P st,
 pred_task_term_occur r st = 0 ->
 In r (pred_domain st) ->
 pred_free_occur r (prop_sub st P) = 0.
Proof.
  induction P; intros; simpl; try rewrite IHP; try rewrite IHP1; try rewrite IHP2; try congruence; auto.
  + now apply atom_sub_aux_pred_not_free_occur_if_substed. 
  + destruct (task_term_occur x (reducev x st) ); simpl; apply IHP; simpl; rew;now rewrite reducev_pred_domain.
  + destruct (task_term_occur x (reducev x st) ); simpl; apply IHP; simpl; rew;now rewrite reducev_pred_domain.
  + destruct (pred_task_term_occur r0 (reducer r0 st)).
      - simpl.  rewrite IHP1; rew. 
        2: now rewrite vars_new_st_pred_domain.
         cname. apply IHP2. now apply reducer_no_pred_task_term_occur. 
         now apply in_pred_domain_reducer_other_iff.
      -  simpl.  rewrite IHP1; rew. 
         2: now rewrite vars_new_st_pred_domain.
         cname. apply IHP2. simpl.  unfold pred_occur. cname. now rewrite reducer_no_pred_task_term_occur.
         simpl. destruct (R.eq_dec r0 r). now left. right. 
         apply in_pred_domain_reducer_other_iff. congruence. easy.
Qed.

Lemma prop_var_sub_keep_closed: forall P st,
  Forall only_var_sub st ->
  closed P ->
  closed (prop_var_sub st P).
Proof. unfold closed. intros. now apply prop_var_sub_keep_no_pred_free_occur. Qed.

Corollary preddef_unfold_keep_no_pred_free_occur: forall r0 r xs P Q,
  pred_free_occur r0 [[let r xs:= P in Q]] = 0 ->
  pred_free_occur r0 (prop_sub [(sprop r xs P)] Q) = 0.
Proof.
  intros. simpl in H. cname.
  + apply pred_not_free_occur_if_substed.
      simpl. easy. now left.
  + zero_r H. apply prop_sub_keep_no_pred_free_occur.
      simpl. now rewrite H. easy.
Qed.

Corollary preddef_unfold_keep_closed: forall r xs P Q,
  closed [[let r xs := P in Q]] ->
  closed (prop_sub [(sprop r xs P)] Q).
Proof.  intros. hnf in *. intros. apply preddef_unfold_keep_no_pred_free_occur. auto. Qed.

(*                                                                   *)
(*  Fixpoint edition                                           *)
(*                                                                   *)
Fixpoint prop_pred (d:prop): list R.t :=
  match d with
  | [[¬ P]] => prop_pred P
  | PAtom a => [atom_pred a]
  | [[∀x, P]] 
  | [[∃x, P]]=> prop_pred P
  | [[P1 /\ P2]]
  | [[P1 \/ P2]]
  | [[P1 -> P2]]
  | [[P1 <-> P2]] => prop_pred P1 ++ prop_pred P2
  | PPredDef r xs P Q => r::prop_pred P ++ prop_pred Q
  | _ => nil
  end.
  
Fixpoint preds_no_free_occur (rs: list R.t) (P:prop):=
  match rs with
  | nil => true
  | r::rs0 => match pred_free_occur r P with
                  | O => preds_no_free_occur rs0 P
                  | _ => false
                  end
 end.

Lemma closed_then_preds_no_free_occur_true: forall rs P,
  closed P ->
  preds_no_free_occur rs P = true.
Proof.
  intros. unfold closed in H. induction rs.
  + easy.
  + simpl. now rewrite H.
Qed. 
 
Lemma not_in_prop_pred_then_no_pred_free_occur: forall r P,
  ~ In r (prop_pred P) ->
  pred_free_occur r P = 0.
Proof.
  induction P; intros; try tauto; simpl in *; des_notin H; try rewrite IHP1; try easy; try rewrite IHP2; try easy.
  +  apply not_atom_pred_no_pred_atom_occur. congruence.     
  +  cname. 
Qed.     

Lemma preds_no_free_occur_correct: forall rs P,
   preds_no_free_occur rs P = true <->
   (forall r , In r rs -> pred_free_occur r P = 0).
Proof.
  split; intros. 
  + induction rs; intros.
     - inversion H0.
     - simpl in H.  destruct (pred_free_occur a P) eqn: E.
        * destruct H0. subst. easy. now  apply IHrs.
        * discriminate.
  + induction rs.
        - easy.
        - simpl. rewrite H. 2: now left. apply IHrs. intros. apply H. now right. 
Qed.

Definition closedb (d:prop): bool:=
  preds_no_free_occur (prop_pred d) d.
  
Lemma closed_closedb: forall d,
  closed d <->  closedb d = true.
Proof.
  split; intros.
  + now apply closed_then_preds_no_free_occur_true.  
  + unfold closed; intros. unfold closedb in H. destruct (in_preds_dec r (prop_pred d)).
     - eapply preds_no_free_occur_correct. 2: apply i. easy.
     - now apply not_in_prop_pred_then_no_pred_free_occur.
Qed.   

Local Ltac closed_proof:= let r:= fresh "r" in let H:= fresh "H" in let H0:= fresh "H" in 
  split; intros; [split; hnf in *; intros; specialize H with r; zero_r H|
  destruct H; hnf in *; intros; specialize H with r; specialize H0 with r; simpl; now rewrite H].
  
Lemma PImpl_keep_closed: forall P Q,
  closed [[P ->Q]] <-> closed P /\ closed Q.
Proof. closed_proof. Qed.

Lemma PAnd_keep_closed: forall P Q,
  closed [[P /\ Q]] <-> closed P /\ closed Q.
Proof. closed_proof. Qed.

Lemma POr_keep_closed: forall P Q,
  closed [[P \/ Q]] <-> closed P /\ closed Q.
Proof. closed_proof. Qed.

Lemma PIff_keep_closed: forall P Q,
  closed [[P <-> Q]] <-> closed P /\ closed Q.
Proof. closed_proof. Qed.

Lemma PNot_keep_closed: forall P,
  closed [[¬ P]] <-> closed P.
Proof. intros. unfold closed. now simpl. Qed.

Lemma PForall_keep_closed: forall x P,
  closed [[∀ x, P]] <-> closed P.
Proof. intros. unfold closed. now simpl. Qed.

Lemma PExists_keep_closed: forall x P,
  closed [[∃ x, P]] <-> closed P.
Proof. intros. unfold closed. now simpl. Qed.

Lemma PPredDef_closed: forall r xs P Q,
  closed [[let r xs:= P in Q]] ->
  closed P /\ (forall r0, r<> r0 -> pred_free_occur r0 Q = 0).
Proof.
  intros. hnf in H. simpl in H. split.
  + hnf. intros. specialize H with r0. zero_r H.
  + intros. specialize H with r0. cname. zero_r H.
Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*            Naive                                               *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)
(** Naive: No atom and preddef, classic FOL prop **)
Inductive naive: prop -> Prop:=
 | PEq_naive: forall t1 t2, naive [[t1 = t2]]
 | PRel_naive: forall t1 t2, naive [[t1 ∈ t2]] 
 | PTrue_naive: naive PTrue 
 | PFalse_naive:naive PFalse 
 | PNot_naive: forall P,
        naive P ->
        naive [[¬P]] 
 | PAnd_naive: forall  P1 P2,
        naive P1  ->
        naive P2  ->
        naive [[P1 /\ P2]] 
  | POr_naive: forall  P1 P2,
        naive P1  ->
        naive P2  ->
        naive [[P1 \/ P2]] 
  | PImpl_naive: forall  P1 P2,
        naive P1  ->
        naive P2  ->
        naive [[P1 -> P2]] 
  | PIff_naive: forall  P1 P2,
        naive P1  ->
        naive P2  ->
        naive [[P1 <-> P2]] 
  | PForalls_naive: forall  x P,
       naive P  ->
       naive [[∀x,P]] 
  | PExists_naive: forall  x P,
       naive P  ->
       naive [[∃x,P]] 
 .

Lemma naive_no_pred: forall r P,
  naive P ->
  pred_free_occur r P = O.
Proof.  intros. induction H; simpl; try rewrite IHnaive1; try rewrite IHnaive2; try congruence; easy. Qed.
  
Lemma prop_var_sub_keep_naive_iff: forall st P,
  naive P <-> naive (prop_var_sub st P).
Proof.
  split; intros. 
  + revert st. induction H; intros; simpl; try now constructor.
       - destruct ( task_term_occur x (reducev x st)); constructor; auto.
       - destruct ( task_term_occur x (reducev x st)); constructor; auto.
  + revert st H. induction P; intros; try constructor; simpl in H;[ try inversion H; subst; try eapply IHP; eauto.. |idtac|idtac|idtac]. 
       - destruct ( task_term_occur x (reducev x st)); inversion H; subst; eapply IHP; eauto.
       - destruct ( task_term_occur x (reducev x st)); inversion H; subst; eapply IHP; eauto.
       - inversion H.
Qed.

Lemma instantiate_var_binder_keep_naive_iff: forall xs st P,
  naive P <-> naive (instantiate_var_binder P xs st).
Proof.
  split; intros.  
  + revert xs P H. induction st; intros; destruct xs; try easy.
      apply IHst. now apply prop_var_sub_keep_naive_iff.
  + revert xs P H. induction st; intros; destruct xs; try easy.
      simpl in H. apply IHst in H. erewrite prop_var_sub_keep_naive_iff; eauto.
Qed.

Lemma naive_alpha_eq: forall p q bd, 
  naive p ->
  alpha_eq bd p q ->
  naive q.
Proof. intros. revert H. induction H0; intros; try constructor; try inversion H; subst; auto; try inversion H0. Qed.

Corollary naive_aeq: forall P Q,
  aeq P Q -> naive P -> naive Q.
Proof.  intros. eapply naive_alpha_eq. eauto. apply H.  Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Atom_naive                                               *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *) 

(**  Atom_naive: no preddef **)
Inductive atom_naive: prop -> Prop:=
 | PEq_atom_naive: forall t1 t2, atom_naive [[t1 = t2]]
 | PRel_atom_naive: forall t1 t2, atom_naive [[t1 ∈ t2]]
 | PAtom_atom_naive: forall a, atom_naive (PAtom a) 
 | PTrue_atom_naive: atom_naive PTrue 
 | PFalse_atom_naive:atom_naive PFalse 
 | PNot_atom_naive: forall P,
        atom_naive P ->
        atom_naive [[¬P]] 
 | PAnd_atom_naive: forall  P1 P2,
        atom_naive P1  ->
        atom_naive P2  ->
        atom_naive [[P1 /\ P2]] 
  | POr_atom_naive: forall  P1 P2,
        atom_naive P1  ->
        atom_naive P2  ->
        atom_naive [[P1 \/ P2]] 
  | PImpl_atom_naive: forall  P1 P2,
        atom_naive P1  ->
        atom_naive P2  ->
        atom_naive [[P1 -> P2]] 
  | PIff_atom_naive: forall  P1 P2,
        atom_naive P1  ->
        atom_naive P2  ->
        atom_naive [[P1 <-> P2]] 
  | PForalls_atom_naive: forall  x P,
       atom_naive P  ->
       atom_naive [[∀x,P]] 
  | PExists_atom_naive: forall  x P,
       atom_naive P  ->
       atom_naive [[∃x,P]] 
.

(*                                                                   *)
(*  Fixpoint edition                                           *)
(*                                                                   *)

Fixpoint atom_naiveb(p:prop):bool:=
  match p with
  | PNot P => atom_naiveb P
  | PAnd P1 P2 
  | POr P1 P2
  | PImpl P1 P2
  | PIff P1 P2 => atom_naiveb P1 && atom_naiveb P2
  | PForall _ P 
  | PExists _ P => atom_naiveb P
  | PPredDef _ _ _ _ => false
  | _ => true
  end.
  
Lemma atom_naive_atom_naiveb: forall P,
  atom_naive P <-> atom_naiveb P = true.
Proof.
  split.
  + intros. induction H; intros; simpl; try congruence; now apply andb_true_iff.
  + induction P; intros; try constructor; simpl in H; try apply andb_true_iff in H; try tauto. discriminate H. 
Qed.  

(*                                                                   *)
(*  Lemmas about atom_naive                         *)
(*                                                                   *)

Definition sprop_atom_naive (st:subst_pair):=
  match st with
  | sprop r xs P => atom_naive P
  | _ => True
  end.
  

Lemma prop_var_sub_keep_atom_naive: forall P st,
  atom_naive P ->
  atom_naive (prop_var_sub st P).
Proof.
   induction P; intros; try inversion H; subst; simpl; try repeat constructor; auto.
   + destruct (task_term_occur x (reducev x st)); constructor; now apply IHP.
   + destruct (task_term_occur x (reducev x st)); constructor; now apply IHP.
Qed.

Lemma instantiate_var_binder_keep_atom_naive: forall P xs ts,
  atom_naive P ->
  atom_naive (instantiate_var_binder P xs ts).
Proof.
  intros. revert P H xs. induction ts; intros; destruct xs; try easy.
  simpl. specialize IHts with (prop_var_sub (vars_new_st P xs [(svar t a)]) P) (vars_new_xs P xs [(svar t a)]).
  apply IHts. now apply prop_var_sub_keep_atom_naive.
Qed.  

Lemma extend_pred_atom_naive: forall r ts st,
  Forall sprop_atom_naive st ->
  atom_naive (extend_pred r ts st).
Proof.
  intros. revert r ts. induction st; intros.
  + simpl. constructor.
  + destruct a.
      - simpl. apply IHst. now forall_cons H.
      - simpl. cname.
        * constructor.
        * apply IHst. now forall_cons H.
      - simpl. cname.
        * apply instantiate_var_binder_keep_atom_naive. forall_cons H. easy. 
        * apply IHst. now forall_cons H.
Qed.
      

Lemma atom_sub_aux_atom_naive: forall a st ts,
  Forall sprop_atom_naive st ->
  atom_naive (atom_sub_aux a ts st).
Proof.
  induction a; intros.
  + simpl. now apply extend_pred_atom_naive.
  + simpl. now apply IHa.
Qed. 

Lemma prop_sub_atom_naive: forall P st,
  Forall sprop_atom_naive st ->
  atom_naive P ->
  atom_naive (prop_sub st P).
Proof.
  induction P; intros; try inversion H0; subst; simpl; try repeat constructor; auto.
  + now apply atom_sub_aux_atom_naive. 
  + destruct (task_term_occur x (reducev x st) ).
      - constructor. apply IHP. now apply reducev_Forall. easy.
      - constructor.  apply IHP. apply Forall_cons. constructor. now apply reducev_Forall. easy. 
    + destruct (task_term_occur x (reducev x st) ).
      - constructor. apply IHP. now apply reducev_Forall. easy.
      - constructor.  apply IHP. apply Forall_cons. constructor. now apply reducev_Forall. easy. 
Qed.

Lemma vars_new_st_sprop_atom_naive: forall xs st P, 
  Forall sprop_atom_naive st ->
  Forall sprop_atom_naive (vars_new_st P xs st).
Proof.
  induction xs; intros.
  + easy.
  + simpl. destruct (task_term_occur a (reducev a st) ).
      - apply IHxs. now apply reducev_Forall.
      - apply IHxs. apply Forall_cons. exact I. now apply reducev_Forall.
Qed.

Lemma naive_is_atom_naive: forall P,
  naive P ->  atom_naive P.
Proof. intros. induction H; now constructor. Qed.

Lemma closed_atom_naive_is_naive: forall P,
  closed P ->
  atom_naive P ->
  naive P.
Proof.
  intros. induction H0;[ constructor| constructor |idtac |try constructor;try apply IHatom_naive1; try apply IHatom_naive2;
   hnf in *; intros; try specialize H with r; zero_r H..|idtac|idtac].
  + exfalso. induction a.
      - unfold closed in H. specialize H with r.
         simpl in H. cname.
      - apply IHa. hnf. intros. apply H.
  + constructor. unfold closed in H. simpl in H. tauto.
  + constructor. unfold closed in H. simpl in H. tauto.
Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Legal and pred_legal                                            *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

(** Record the number of arguments for each predicate **)
Definition pred_arg: Type:= R.t * nat.

Definition pred_args: Type:= list pred_arg.

Definition args_domain (args:pred_args):list R.t:=
  map fst args.

(**  If the atom is in pred args, the number of terms and the number of arguments should be the same**)
Fixpoint atom_legal (a: atom) (args:pred_args): Prop:=
  match args with
  | nil => True
  | (r,n)::args0 => if R.eq_dec (atom_pred a) r then atom_length a = n
                              else atom_legal a args0
  end.

Fixpoint reduce_arg (r:R.t) (args:pred_args):pred_args:=
  match args with
  | nil => nil
  | (r0,xs)::args0 => if R.eq_dec r r0 then (reduce_arg r args0) else (r0,xs)::(reduce_arg r args0)
end.

Fixpoint subst_task_to_pred_args (st:subst_task): pred_args:=
  match st with
  | nil => nil
  | (sprop r xs P):: st0 => (r,length xs)::(subst_task_to_pred_args st0)
  | _:: st0 => subst_task_to_pred_args st0
  end.
 
(**  Predicate in all atoms are used correctly according to pred_args **)
Inductive pred_legal: prop -> pred_args ->Prop:=
 | PEq_legal: forall args t1 t2, pred_legal [[t1 = t2]] args
 | PRel_legal: forall args t1 t2, pred_legal [[t1 ∈ t2]] args
 | PAtom_legal: forall args a,
      atom_legal a args ->
      pred_legal (PAtom a) args
 | PTrue_legal: forall args, pred_legal PTrue args
 | PFalse_legal: forall args, pred_legal PFalse args
 | PNot_leagl: forall args P,
        pred_legal P args ->
        pred_legal [[¬P]] args
 | PAnd_legal: forall args P1 P2,
        pred_legal P1 args ->
        pred_legal P2 args ->
        pred_legal [[P1 /\ P2]] args
  | POr_legal: forall args P1 P2,
        pred_legal P1 args ->
        pred_legal P2 args ->
        pred_legal [[P1 \/ P2]] args
  | PImpl_legal: forall args P1 P2,
        pred_legal P1 args ->
        pred_legal P2 args ->
        pred_legal [[P1 -> P2]] args
  | PIff_legal: forall args P1 P2,
        pred_legal P1 args ->
        pred_legal P2 args ->
        pred_legal [[P1 <-> P2]] args
  | PForalls_legal: forall args x P,
       pred_legal P args ->
       pred_legal [[∀x,P]] args
  | PExists_legal: forall args x P,
       pred_legal P args ->
       pred_legal [[∃x,P]] args
  | PPredDef_legal: forall args r xs P Q,
       pred_legal P args ->
       pred_legal Q ((r,length xs)::(reduce_arg r args)) ->
       pred_legal [[let r xs := P in Q]] args
 .
 
Definition legal (p:prop):= pred_legal p nil.

(*                                                                   *)
(*  Fixpoint edition                                           *)
(*                                                                   *)
 
Fixpoint atom_legalb (a:atom)(args: pred_args):bool:=
  match args with
  | nil => true
  | (r, n):: args0 => if R.eq_dec (atom_pred a) r
                           then Nat.eqb (atom_length a) n
                           else atom_legalb a args0
  end.
  
Lemma atom_legal_atom_legalb: forall a args,
  atom_legal a args <-> atom_legalb a args = true.
Proof.
  split; intros.
  + induction args.
      - easy.
      - destruct a0. simpl in *.  destruct (R.eq_dec (atom_pred a) t).
        * symmetry. apply PeanoNat.Nat.eqb_eq in H. now rewrite H.
        * tauto.
  + induction args.
      - exact I.
      - destruct a0. simpl in *. destruct (R.eq_dec (atom_pred a) t).
        * now apply PeanoNat.Nat.eqb_eq .
        * tauto.
Qed. 

Fixpoint pred_legalb (d:prop)(args:pred_args): bool:=
  match d with
  | PAtom a => atom_legalb  a args
  | [[¬ P]] => pred_legalb P args
  | [[∀ x, P]] 
  | [[∃ x, P]] => pred_legalb P args
  | [[P1 /\ P2]]
  | [[P1 \/ P2]]
  | [[P1 -> P2]]
  | [[P1 <-> P2]] => pred_legalb P1 args && pred_legalb P2 args
  | PPredDef r xs P Q => pred_legalb P args && pred_legalb Q ((r, length xs):: reduce_arg r args)
  | _ => true
  end.
                             
Lemma pred_legal_pred_legalb: forall P args,
  pred_legal P args <-> pred_legalb P args = true.
Proof.
  split; intros.
   + induction H; intros;simpl; try rewrite IHpred_legal;
       try rewrite IHpred_legal1; try rewrite IHpred_legal2;  try easy.  
       now apply atom_legal_atom_legalb.
   + revert args H. induction P; intros; simpl in H; try apply andb_prop in H; 
      match type of H with
      | _ /\ _ => destruct H
      | _ => idtac
      end; constructor; auto.
      now apply atom_legal_atom_legalb.
Qed.

Definition legalb (d:prop):bool:= pred_legalb d nil.

Lemma legal_legalb: forall P,
  legal P <-> legalb P = true.
Proof. intros. now apply pred_legal_pred_legalb. Qed.
 
(*                                                                   *)
(*  Lemmas about pred_legal                           *)
(*                                                                   *) 
 
Lemma reduce_arg_atom_legal_other: forall r a args,
  r <> atom_pred a ->
  atom_legal a (reduce_arg r args) ->
  atom_legal a args.
Proof.
  induction args; intros. easy.
  destruct a0. simpl in H0. cname. simpl in H0. cname. 
  simpl in H0. cname.
Qed.
 
Lemma naive_pred_legal: forall P args,
  naive P ->
  pred_legal P args.
Proof. intros. induction H; try now constructor. Qed.

Corollary naive_legal: forall P,
  naive P -> legal P.
Proof. intros. now apply naive_pred_legal. Qed.
 
Lemma reducev_subst_task_to_pred_args: forall x st,
  subst_task_to_pred_args (reducev x st) = subst_task_to_pred_args st.
Proof. induction st. easy. destruct a; cname. Qed.    

Lemma reducer_subst_task_to_pred_args: forall x st,
  subst_task_to_pred_args (reducer x st) = reduce_arg x (subst_task_to_pred_args st).
Proof. induction st. easy. destruct a; cname. simpl. cname. Qed.      
 
Lemma reduce_arg_atom_pred_legal: forall a args,
  atom_legal a (reduce_arg (atom_pred a) args).
Proof.
  intros. induction args.
  + constructor.
  + destruct a0 as [r xs]. simpl. cname. 
      simpl. destruct (R.eq_dec (atom_pred a) r); congruence.
Qed.
 
Lemma reduce_arg_reduce_arg: forall r args,
  reduce_arg r (reduce_arg r args) = reduce_arg r args.
Proof. induction args. easy.  destruct a; cname. simpl. cname. Qed.  

Lemma reduce_arg_swap: forall r1 r2 args,
  reduce_arg r1 (reduce_arg r2 args) =  reduce_arg r2 (reduce_arg r1 args).
Proof. induction args. easy. destruct a; cname; simpl; cname. Qed.

Lemma reduce_arg_app: forall r args1 args2,
  reduce_arg r (args1++args2) = reduce_arg r args1 ++ reduce_arg r args2.
Proof.
  intros. induction args1.
  + easy.
  + simpl. destruct a. cname. now rewrite IHargs1.
Qed.
  
Lemma reduce_arg_pred_legal: forall r args P,
  pred_legal P args ->
  pred_legal P (reduce_arg r args).
Proof.
  intros. revert args H. induction P; intros; try inversion H; subst; try constructor; auto.
  +  clear H. induction args. easy. destruct a0 as [r0 xs].
       simpl. simpl in H1. destruct (R.eq_dec (atom_pred a) r0) in H1; cname.
       - subst. apply reduce_arg_atom_pred_legal.
       - simpl. cname. 
       - simpl. cname. 
  + destruct (R.eq_dec r r0).
      - subst r0. now rewrite reduce_arg_reduce_arg.
      - specialize IHP2 with ((r0,length xs)::(reduce_arg r0 args)).
        simpl in IHP2. destruct (R.eq_dec r r0) in IHP2. congruence.
        rewrite reduce_arg_swap. tauto.
Qed.

Lemma atom_pred_pred_atom_occur: forall a,
  pred_atom_occur (atom_pred a) a = S O.
Proof. induction a; cname. Qed.


Lemma reduce_arg_pred_legal_other: forall r P args,
  pred_free_occur r P = 0 ->
  pred_legal P (reduce_arg r args) ->
  pred_legal P args.
Proof.
  induction P; intros; zero_r H; inversion H0; subst; constructor; auto.
  + clear H0. induction args.
      - constructor.
      - destruct a0 as [r0 n]. simpl in H2. cname.
        * rewrite atom_pred_pred_atom_occur in H. discriminate H.
        * simpl in H2. cname.
        * simpl in H2. cname.
  + cname.
      - now rewrite reduce_arg_reduce_arg in H8.
      - apply IHP2. easy. simpl. cname. now rewrite reduce_arg_swap. 
Qed.

Lemma not_in_reduce_arg_domain: forall r args,
  ~ In r (args_domain (reduce_arg r args)).
Proof.
  induction args.
  + easy.
  + destruct a. simpl. cname.
      simpl. now apply not_in_cons.
Qed.
      
Lemma in_reduce_arg_domian: forall r1 r2 args,
  In r1 (args_domain (reduce_arg r2 args)) ->
  In r1 (args_domain args).
Proof.
  intros. induction args.
  + inversion H.
  + destruct a. simpl. simpl in H. cname. 
      simpl in H. tauto.
Qed.   


Lemma irrelevent_pred_legal_app: forall P args1 args2,
  (forall r, In r (args_domain args2) -> pred_free_occur r P = 0) ->
  pred_legal P args1 -> 
  pred_legal P (args1++args2).
Proof.
  intros. revert args1 args2 H H0. induction P; intros; inversion H0; subst; try constructor.
  + clear H0. simpl in H.  revert args2 a H H2. induction args1; intros.
      - simpl. clear H2. induction args2.
        * easy.
        * destruct a0.  cname.
            ++ specialize H with (atom_pred a). simpl in H. 
                   assert (pred_atom_occur (atom_pred a) a = 0) by tauto.
                   pose proof atom_pred_pred_atom_occur a. 
                   rewrite H0 in H1. discriminate.
            ++ apply IHargs2. intros. apply H. now right.
      - destruct a. simpl. simpl in H2. cname. apply IHargs1;auto. 
  + apply IHP. intros. simpl in H. auto. easy.
  + apply IHP1. intros. apply H in H1. zero_r H1. easy.
  + apply IHP2. intros. apply H in H1. zero_r H1. easy.
  + apply IHP1. intros. apply H in H1. zero_r H1. easy.
  + apply IHP2. intros. apply H in H1. zero_r H1. easy.
  + apply IHP1. intros. apply H in H1. zero_r H1. easy.
  + apply IHP2. intros. apply H in H1. zero_r H1. easy.
  + apply IHP1. intros. apply H in H1. zero_r H1. easy.
  + apply IHP2. intros. apply H in H1. zero_r H1. easy.
  + apply IHP. intros. simpl in H. auto. easy.
  + apply IHP. intros. simpl in H. auto. easy.
  + apply IHP1. intros. apply H in H1. zero_r H1. easy.
  + rewrite reduce_arg_app. eapply IHP2 in H7. apply H7. intros.
      destruct (R.eq_dec r0 r).
      - subst. pose proof not_in_reduce_arg_domain r args2. contradiction.
      - apply in_reduce_arg_domian in H1. apply H in H1. simpl in H1.
         cname.  zero_r H1.
Qed.

Corollary irrelevant_pred_legal: forall P args,
  (forall r, In r (args_domain args) -> pred_free_occur r P = 0) ->
  pred_legal P nil -> 
  pred_legal P args.
Proof. intros. now apply (irrelevent_pred_legal_app P nil args). Qed.


Lemma construct_atom_legal_length: forall a ts1 ts2 args,
  length ts1 = length ts2 ->
  atom_legal (construct_atom a ts1) args ->
  atom_legal (construct_atom a ts2) args.
Proof.
  intros. revert a ts2 args H H0. induction ts1; intros; destruct ts2; try inversion H.
  + easy.
  + induction args.
      - constructor.
      - destruct a1 as [r0 xs]. simpl. rewrite construct_atom_pred. simpl.
         simpl in H0. rewrite construct_atom_pred in H0. simpl in H0.  destruct (R.eq_dec (atom_pred a0) r0).
         * rewrite construct_atom_length. simpl. rewrite construct_atom_length in H0. simpl in H0. now rewrite <- H2.
         * auto.
Qed.

Lemma prop_var_sub_keep_pred_legal: forall P st args,
  pred_legal P args <-> pred_legal (prop_var_sub st P) args.
Proof.
   intros. split; revert st args. 
   + induction P; intros; simpl; inversion H; subst; try constructor; auto.
       - clear H. revert st. intros.
          induction args. 
          * easy.
          * destruct a0. simpl in *. rewrite atom_var_sub_atom_pred. 
             cname. apply atom_var_sub_length.   
        - destruct (task_term_occur x (reducev x st)); constructor; apply IHP; try easy. 
        - destruct (task_term_occur x (reducev x st)); constructor; apply IHP; try easy. 
        - rew. now apply IHP2. 
     + induction P; intros; try now constructor. 
         - inversion H; subst. clear H. revert st H1. induction args; intros.
           *  repeat constructor. 
           * destruct a0. simpl in *. rewrite atom_var_sub_atom_pred in H1. constructor. simpl. cname.
              now rewrite atom_var_sub_length. apply IHargs in H1;try easy. now inversion H1. 
         - simpl in H. inversion H; subst. constructor; eauto.
         - simpl in H. inversion H; subst. constructor; eauto.
         - simpl in H. inversion H; subst. constructor; eauto.
         - simpl in H. inversion H; subst. constructor; eauto.
         - simpl in H. inversion H; subst. constructor; eauto.
         - constructor. simpl in H. destruct (task_term_occur x (reducev x st)); inversion H; subst; eapply IHP; apply H3. 
         - constructor. simpl in H. destruct (task_term_occur x (reducev x st)); inversion H; subst; eapply IHP; apply H3. 
          - simpl in H. inversion H; subst. rew. constructor.  now apply IHP1 in H5. now apply IHP2 in H6.
Qed.  

Corollary instantiate_var_binder_keep_pred_legal: forall xs ts P args,
  pred_legal P args <-> pred_legal (instantiate_var_binder P xs ts) args.
Proof.
  split; intros; revert xs P args H.
  + induction ts; intros.
      - now destruct xs. 
      - destruct xs. easy. simpl. apply IHts. now apply prop_var_sub_keep_pred_legal.
  + induction ts; intros.
      - now destruct xs. 
      - destruct xs. easy. simpl in *. apply IHts in H. now apply prop_var_sub_keep_pred_legal in H.
Qed.  

Lemma extend_pred_get_pred_sub_keep_pred_legal: forall r ts1 ts2 st args,
  length ts1 = length ts2 ->
  (pred_legal (extend_pred r ts1 (get_pred_sub st)) args <-> pred_legal (extend_pred r ts2 st) args).
Proof. 
  split; intros.
  + induction st. simpl in *. inversion H0; subst. constructor. eapply construct_atom_legal_length. apply H. easy. 
      destruct a; simpl in *.
      - tauto.
      - cname. inversion H0; subst. constructor. eapply construct_atom_legal_length. apply H. easy.
      - cname. apply instantiate_var_binder_keep_pred_legal in H0. now apply instantiate_var_binder_keep_pred_legal.
  + induction st. simpl in *.  inversion H0; subst. constructor. eapply construct_atom_legal_length. symmetry. apply H. easy.
      destruct a; simpl in *.
      - tauto.
      - cname. inversion H0; subst. constructor. eapply construct_atom_legal_length.  symmetry. apply H. easy.
      - cname. apply instantiate_var_binder_keep_pred_legal in H0. now apply instantiate_var_binder_keep_pred_legal.
Qed.
     
Corollary atom_sub_aux_get_pred_sub_keep_pred_legal: forall a ts1 ts2 st args,
  length ts1 = length ts2 ->
  (pred_legal (atom_sub_aux a ts1 (get_pred_sub st)) args <-> pred_legal (atom_sub_aux a ts2 st) args).
Proof. 
  induction a; intros. simpl. now apply extend_pred_get_pred_sub_keep_pred_legal.
  simpl. apply IHa. simpl. now f_equal.   
Qed.

Lemma prop_sub_get_pred_sub_keep_pred_legal: forall P st args,
  pred_legal (prop_sub (get_pred_sub st) P) args <->
  pred_legal (prop_sub st P) args.
Proof.
  induction P; intros.
  + split; intros; simpl; constructor.
  + split; intros; simpl; constructor.
  + now apply  atom_sub_aux_get_pred_sub_keep_pred_legal.
  + split; intros; simpl; constructor.
  + split; intros; simpl; constructor.
  + split; intros; simpl; inversion H; subst; constructor; apply IHP; auto.
  + split; intros; simpl; inversion H; subst; constructor; try apply IHP1; try apply IHP2; auto.
  + split; intros; simpl; inversion H; subst; constructor; try apply IHP1; try apply IHP2; auto.
  + split; intros; simpl; inversion H; subst; constructor; try apply IHP1; try apply IHP2; auto.
  + split; intros; simpl; inversion H; subst; constructor; try apply IHP1; try apply IHP2; auto.
  + split; intros; simpl in *. 
     - destruct (task_term_occur x (reducev x (get_pred_sub st))); destruct (task_term_occur x (reducev x st)).
       * inversion H; subst. constructor; apply IHP; rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
    - destruct (task_term_occur x (reducev x (get_pred_sub st))); destruct (task_term_occur x (reducev x st)).
       * inversion H; subst. constructor. apply IHP in H3. apply IHP. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
  + split; intros; simpl in *. 
     - destruct (task_term_occur x (reducev x (get_pred_sub st))); destruct (task_term_occur x (reducev x st)).
       * inversion H; subst. constructor; apply IHP; rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
    - destruct (task_term_occur x (reducev x (get_pred_sub st))); destruct (task_term_occur x (reducev x st)).
       * inversion H; subst. constructor. apply IHP in H3. apply IHP. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. rew.
       * inversion H; subst. constructor; apply IHP; simpl; rew. apply IHP in H3. simpl in H3. rew.
  + split; intros; simpl in *; assert (pred_task_term_occur r (reducer r (get_pred_sub st)) =
    pred_task_term_occur r (reducer r st)) by (rewrite <- get_pred_sub_reducer_swap; 
    apply pred_task_term_occur_get_pred_sub).
    - rewrite H0 in H. clear H0. destruct (pred_task_term_occur r (reducer r st)).
      * inversion H; subst. clear H. constructor. apply IHP1; rew.  
          rewrite <- IHP1 in H5. rew. rew.
          rewrite <- get_pred_sub_reducer_swap in H6. now apply IHP2.
      * assert (newr (upred r  :: prop_ustr P2 ++ task_ustr (reducer r (get_pred_sub st))) = newr
           (upred r :: prop_ustr P2 ++ task_ustr (reducer r st))). 
          rewrite 2 newr_FOL_LAM.  simpl. repeat rewrite predname_list_app.
          rewrite <- get_pred_sub_reducer_swap. rew.
          rewrite H0 in H. clear H0. inversion H; subst. clear H. constructor. 
          ++ apply IHP1; rew. rewrite <- IHP1 in H5. rew. 
          ++ rew. apply IHP2. simpl. now rewrite get_pred_sub_reducer_swap.
  - rewrite H0. clear H0.  destruct (pred_task_term_occur r (reducer r st)).
      * inversion H; subst. clear H. rewrite <- IHP1 in H5. rew. constructor.
          ++ apply IHP1; rew.
          ++ rew. rewrite <- get_pred_sub_reducer_swap. now apply IHP2.
      * assert (newr (upred r :: prop_ustr P2 ++ task_ustr (reducer r (get_pred_sub st))) = newr
           (upred r :: prop_ustr P2 ++ task_ustr (reducer r st))).    
           rewrite 2 newr_FOL_LAM.  simpl. repeat rewrite predname_list_app.
           rewrite <- get_pred_sub_reducer_swap. rew. 
        rewrite H0. clear H0. inversion H; subst. clear H. constructor.
        ++ apply IHP1; rew. apply IHP1 in H5. rew.
        ++ rew. rewrite <- get_pred_sub_reducer_swap.  apply IHP2 in H6. now simpl in H6.
Qed.
        

(***  Only extend with naive preddef keep pred legal ***)
Definition sprop_naive (st:subst_pair) :=
  match st with
  | sprop r xs P => naive P 
  | svar _ _ => True
  | spred _ _ => False
  end.

Lemma sprop_naive_no_pred_task_term_occur: forall r st,
  Forall sprop_naive st ->
  pred_task_term_occur r st = O.
Proof.
  induction st; intros. easy. destruct a; forall_cons H.
  + tauto.
  + simpl in H. now exfalso.
  + simpl. simpl in H. rewrite naive_no_pred. tauto. easy.
Qed.    
  
Lemma extend_pred_legal_sprop_naive: forall r st ts args,
  Forall sprop_naive st ->
  atom_legal (construct_atom (APred r) ts) args ->
  pred_legal (extend_pred r ts st) args.
Proof.
  intros. revert r ts args H H0. induction st; intros.
  + simpl. constructor. induction args.
      - easy.
      - destruct a as [r0 n0].
        simpl in H0. simpl. rewrite construct_atom_pred in *. simpl in *. cname.
  + destruct a; forall_cons H.
      - simpl. auto.
      - now exfalso.
      - simpl. simpl in H. cname.
        * assert (naive (instantiate_var_binder P xs ts)) by now apply instantiate_var_binder_keep_naive_iff.
           now apply naive_pred_legal.
        * auto.
Qed.


Lemma atom_sub_aux_pred_legal_sprop_naive: forall a st ts args,
  Forall sprop_naive st ->
  atom_legal (construct_atom a ts) args ->
  pred_legal (atom_sub_aux a ts st) args.
Proof.
  induction a ; intros.
  + now apply extend_pred_legal_sprop_naive.
  + simpl. apply IHa. easy. rewrite construct_atom_app in H0.
      eapply construct_atom_legal_length. 2: apply H0. easy.
Qed.
            
Lemma prop_sub_keep_pred_legal_sprop_naive: forall P st args,
  Forall sprop_naive st ->
  pred_legal P args ->
  pred_legal (prop_sub st P) args.
Proof.
  induction P; intros; simpl; inversion H0; subst; try constructor; auto.
  + now apply atom_sub_aux_pred_legal_sprop_naive. 
  + destruct  ( task_term_occur x (reducev x st)).
      - constructor. apply IHP. now apply reducev_Forall. easy.
      - constructor. apply IHP. apply Forall_cons. easy. now apply reducev_Forall. easy.
  + destruct  ( task_term_occur x (reducev x st)).
      - constructor. apply IHP. now apply reducev_Forall. easy.
      - constructor. apply IHP. apply Forall_cons. easy. now apply reducev_Forall. easy.
  +  assert (pred_task_term_occur r (reducer r st) = 0).
       apply sprop_naive_no_pred_task_term_occur. now apply reducer_Forall.
       rewrite H1. constructor.
       - apply IHP1. 2: easy. 
         clear IHP1 IHP2 P2 args H0 H6 H7 H1. revert st H.
         induction xs; intros.
         * easy.
         * simpl. destruct (task_term_occur a (reducev a st) ).
            ++ apply IHxs. now apply reducev_Forall.
            ++ apply IHxs. apply Forall_cons. easy. now apply reducev_Forall.
       - apply IHP2. now apply reducer_Forall. now rewrite vars_new_xs_length.
Qed.

(**** Lemmas about preddef keep pred_legal**)

Fixpoint renaming_pred_task (rs:list R.t)(us:list (option R.t)): subst_task:=
  match rs,us with
  | nil, nil => nil
  | r::rs0, None::us0 => reducer r (renaming_pred_task rs0 us0)
  | r::rs0, Some u::us0 => spred r u:: reducer r (renaming_pred_task rs0 us0)
  | _ , _ => nil
  end.

(**  Pred_args through layers of preddefs*)
Fixpoint local_args (args:pred_args)(rs:list R.t)(ns:list nat):pred_args:=
  match rs, ns with
  | nil, nil => args
  | r::rs0, n::ns0 => (r,n)::(reduce_arg r (local_args args rs0 ns0))
  | _, _ => nil
  end.

Fixpoint remaining_sprop (r:R.t)(xs:list V.t)(P:prop)(rs:list R.t):subst_task:=
  match rs with
  | nil => [sprop r xs P]
  | r0::rs0 => reducer r0 (remaining_sprop r xs P rs0)
  end.
  
Fixpoint new_args (arg:pred_args) (rs: list R.t) (us: list (option R.t)) (ns: list nat):=
  match rs, us, ns with
  | nil, nil, nil => arg
  | r::rs0, (Some u):: us0, n:: ns0 => (u,n)::(reduce_arg u (new_args arg rs0 us0 ns0))
  | r::rs0, None::us0, n:: ns0 => (r,n)::(reduce_arg r  (new_args arg rs0 us0 ns0))
  | _ , _ , _ => arg
  end.

Inductive good_new_pred: R.t -> list V.t -> prop -> list R.t -> list (option R.t) -> Prop:=
  | good_new_pred_nil: forall r0 xs0 P0, good_new_pred r0 xs0 P0 nil nil
  | good_new_pred_none: forall r0 xs0 P0 r rs us,
      good_new_pred r0 xs0 P0 rs us ->
      pred_task_term_occur r (reducer r (renaming_pred_task rs us++ (remaining_sprop r0 xs0 P0 rs))) = 0 ->
      good_new_pred r0 xs0 P0 (r::rs) (None::us) 
  | good_new_pred_some: forall r0 xs0 P0 r u rs us,
      good_new_pred r0 xs0 P0 rs us ->
      r <> u ->
      pred_task_term_occur u (reducer r (renaming_pred_task rs us++ (remaining_sprop r0 xs0 P0 rs)))= 0 ->
      good_new_pred r0 xs0 P0 (r::rs) (Some u::us)
 .

Lemma renaming_pred_task_no_var_sub: forall rs us,
  Forall no_var_sub (renaming_pred_task rs us).
Proof.
  intros. revert us. induction rs; intros.
  + simpl. now destruct us.
  + destruct us. simpl. constructor. simpl. destruct o.
      - apply Forall_cons. constructor. apply reducer_no_var_sub. apply IHrs.
      - apply reducer_no_var_sub. apply IHrs.
Qed.

Lemma remaining_sprop_no_var_sub: forall r xs P rs,
  Forall no_var_sub (remaining_sprop r xs P rs).
Proof.
  intros. induction rs; intros.
  + simpl. repeat constructor.
  + cname. now apply reducer_Forall.
Qed.

Lemma remaining_sprop_reducer: forall r xs P rs,
  reducer r (remaining_sprop r xs P rs) = nil.
Proof. induction rs; intros. simpl. cname. simpl. rewrite reducer_swap. now rewrite IHrs. Qed.

Lemma remaining_sprop_reducer_other: forall r r0 xs P rs,
  r <> r0 ->
  reducer r0 (remaining_sprop r xs P rs) = remaining_sprop r xs P rs.
Proof. induction rs; intros; cname. rewrite reducer_swap. now rewrite IHrs. Qed.

Lemma in_reducer_spred_iff: forall r x r0 st,
   r <> r0 ->
   In (spred r x) st <-> In (spred r x) (reducer r0 st).
Proof.
  induction st; intros. tauto. destruct a; simpl; try tauto.
  + split; intros; cname; destruct H0; try congruence; try tauto. now left. right. tauto.
  + split; intros; simpl in * ;cname; destruct H0; try congruence; try tauto. right. tauto.
Qed.

Lemma atom_sub_aux_wrong_sprop: forall a ts r xs P,
   r <> (atom_pred a) ->
   atom_sub_aux a ts [sprop r xs P] = PAtom (construct_atom a ts).
Proof.
  induction a; intros.
  + simpl. cname.
  + simpl. rewrite IHa. rewrite term_sub_no_var_sub. easy. repeat constructor. easy. 
Qed.
  
Corollary atom_sub_wrong_sprop: forall a r xs P,
   r <> (atom_pred a) ->
   atom_sub  [sprop r xs P] a = PAtom a.
Proof. intros. now apply atom_sub_aux_wrong_sprop. Qed.  

Lemma atom_sub_aux_correct_spred: forall a st ts r r' ,
  atom_pred a = r ->
  atom_sub_aux a ts (spred r r'::st) = PAtom (construct_atom (APred r') ((map (term_sub (spred r r'::st))(atom_terms a))++ts)).
Proof.
  induction a ; intros.
  + cname.
  + simpl. specialize IHa with st ((term_sub (spred r r'::st) t)::ts) r r'. rewrite IHa; try easy.
     rewrite map_app. now rewrite app_assoc_reverse. 
Qed.

Lemma atom_sub_aux_correct_sprop: forall a st ts r xs P,
   atom_pred a = r ->
   atom_sub_aux a ts (sprop r xs P::st) = instantiate_var_binder P xs ((map (term_sub(sprop r xs P::st)) (atom_terms a) )++ ts).
Proof.
  induction a; intros.
  + cname.
  + simpl. specialize IHa with st ((term_sub (sprop r xs P::st) t)::ts) r xs P. rewrite IHa; try easy. rewrite map_app.
      now rewrite app_assoc_reverse. 
Qed. 

Lemma atom_sub_aux_no_pred_change: forall a st ts,
  ~ In (atom_pred a) (pred_domain st) ->
   atom_sub_aux a ts st = PAtom (construct_atom (APred (atom_pred a)) ((map (term_sub st)(atom_terms a))++ts)).
Proof.
  induction a; intros.
  + induction st. easy. destruct a.
     - tauto.
     - simpl in H. cname.
     - simpl in H. cname.
  + specialize IHa with st (term_sub st t::ts). simpl. rewrite IHa; try easy.
      rewrite map_app. now rewrite app_assoc_reverse.
Qed.

Lemma preddef_unfold_keep_pred_legal_lemma: forall Q r xs P rs us ns args,
  pred_legal P args ->
  length rs = length us ->
  length rs = length ns ->
  good_new_pred r xs P rs us ->
 (forall x, In (Some x) us -> pred_occur x Q = 0) ->
  pred_legal Q ( local_args ((r, length xs)::reduce_arg r args) rs ns) ->
  pred_legal (prop_sub ((renaming_pred_task rs us)++ (remaining_sprop r xs P rs)) Q)(new_args args rs us ns).
Proof.
  induction Q; intros.
  + constructor. 
  + constructor.
  + inversion H4; subst. clear H4. revert a us ns args H H0 H1 H2 H3 H6. induction rs; intros;destruct us; destruct ns; try inversion H0; try inversion H1.
     - clear H0 H1 H2 H3. simpl in *. cname.
        * unfold atom_sub. rewrite atom_sub_aux_correct_sprop. now apply instantiate_var_binder_keep_pred_legal. easy. 
        * rewrite atom_sub_wrong_sprop; try congruence. constructor. eapply reduce_arg_atom_legal_other; eauto.
     - simpl in H6. destruct o.
        * inversion H2; subst. clear H2. simpl in *. destruct (R.eq_dec (atom_pred a0) a).  
          ++ subst. unfold atom_sub. rewrite atom_sub_aux_correct_spred; try easy. constructor.
                 simpl. rewrite construct_atom_pred. simpl. cname. rew. rewrite construct_atom_length.
                 simpl. rewrite map_length. apply atom_terms_length.
          ++ rename a into f, t into f'. specialize IHrs with a0 us ns args. apply IHrs in H14; try auto.
                2:{ eapply reduce_arg_atom_legal_other; eauto. }
                clear IHrs H0 H1. erewrite <- atom_sub_reducer_other; eauto. simpl. destruct (R.eq_dec f f); try congruence. 
                rewrite reducer_app. repeat rewrite reducer_reducer. erewrite <- atom_sub_reducer_other in H14; eauto.  
                assert (pred_free_occur f'  (atom_sub (reducer f (renaming_pred_task rs us) ++  reducer f
               (remaining_sprop r xs P rs)) a0)= 0).
               { apply atom_sub_aux_keep_no_pred_free_occur. now rewrite <- reducer_app. auto. }
               eapply reduce_arg_pred_legal_other; eauto. simpl. cname. rewrite reduce_arg_reduce_arg.
               rewrite <- reducer_app. now apply reduce_arg_pred_legal. 
        * inversion H2; subst. clear H2. simpl in *. destruct (R.eq_dec (atom_pred a0) a).
           ++ subst. unfold atom_sub. rewrite atom_sub_aux_no_pred_change. constructor.
                  simpl. rewrite construct_atom_pred. cname. rewrite construct_atom_length.
                  simpl. rew. rewrite map_length. apply atom_terms_length. 
                  rewrite <- reducer_app. apply not_in_reducer_self_pred_domian.
           ++ specialize IHrs with a0 us ns args. apply IHrs in H13; try auto.
                 2:{ eapply reduce_arg_atom_legal_other; eauto. }
                  clear IHrs H0 H1.  erewrite <- atom_sub_reducer_other in H13; eauto.
                  assert (pred_free_occur a  (atom_sub (reducer a (renaming_pred_task rs us) ++  reducer a
               (remaining_sprop r xs P rs)) a0)= 0).
               { apply atom_sub_aux_keep_no_pred_free_occur. now rewrite <- reducer_app. auto. 
                  apply not_atom_pred_no_pred_atom_occur. cname. }
                  eapply reduce_arg_pred_legal_other; eauto.  cname. rewrite reduce_arg_reduce_arg.
               rewrite <- reducer_app. now apply reduce_arg_pred_legal. 
  + constructor.
  + constructor.
  + simpl. constructor. apply IHQ; try easy. now inversion H4.
  + simpl. inversion H4; subst. constructor. apply IHQ1; try easy. intros. apply H3 in H5. 
      zero_r H5. apply IHQ2; try easy. intros. apply H3 in H5. zero_r H5.
  + simpl. inversion H4; subst. constructor. apply IHQ1; try easy. intros. apply H3 in H5. 
      zero_r H5. apply IHQ2; try easy. intros. apply H3 in H5. zero_r H5.
  + simpl. inversion H4; subst. constructor. apply IHQ1; try easy. intros. apply H3 in H5. 
      zero_r H5. apply IHQ2; try easy. intros. apply H3 in H5. zero_r H5.
  + simpl. inversion H4; subst. constructor. apply IHQ1; try easy. intros. apply H3 in H5. 
      zero_r H5. apply IHQ2; try easy. intros. apply H3 in H5. zero_r H5.
  + simpl.  inversion H4; subst. clear H4. destruct ( task_term_occur x (reducev x
         (renaming_pred_task rs us ++
          remaining_sprop r xs P rs))).
      - constructor. rewrite reducev_app. rewrite 2 reducev_no_var_sub.
        2: apply remaining_sprop_no_var_sub. 
        2: apply renaming_pred_task_no_var_sub. apply IHQ; try easy.
      - constructor. apply prop_sub_get_pred_sub_keep_pred_legal. simpl. rew.
        rewrite no_var_sub_get_pred_sub. 
        2:{ apply Forall_app. split; [apply renaming_pred_task_no_var_sub| apply remaining_sprop_no_var_sub]. }
        now apply IHQ.
   + simpl.  inversion H4; subst. clear H4. destruct ( task_term_occur x (reducev x
         (renaming_pred_task rs us ++   remaining_sprop r xs P rs))).
      - constructor. rewrite reducev_app. rewrite 2 reducev_no_var_sub.
        2: apply remaining_sprop_no_var_sub. 
        2:apply renaming_pred_task_no_var_sub. apply IHQ; try easy.
      - constructor. apply prop_sub_get_pred_sub_keep_pred_legal. simpl. rew.
        rewrite no_var_sub_get_pred_sub. 
        2:{ apply Forall_app. split; [apply renaming_pred_task_no_var_sub| apply remaining_sprop_no_var_sub]. }
        now apply IHQ.
  + simpl. inversion H4; subst. clear H4. 
      assert (pred_task_term_occur r (renaming_pred_task rs us) = 0).
    { clear IHQ1 IHQ2 r0 xs0 P ns args H H1 H2 H10 H11. revert us  H0 H3. induction rs; intros; destruct us; try inversion H0. easy.
       simpl. destruct o.
       + simpl. specialize H3 with t as H4. assert (In (Some t) (Some t::us)) by now left. apply H4 in H.
          clear H4. zero_r H. unfold pred_occur. cname. apply reducer_no_pred_task_term_occur.
          apply IHrs. now injection H0. intros. apply H3. now right.
       +  apply reducer_no_pred_task_term_occur. apply IHrs. now injection H0. intros. apply H3. now right. }
       
       rewrite reducer_app. rewrite pred_task_term_occur_app. 
       eapply reducer_no_pred_task_term_occur in H4 as H5. rewrite H5. simpl.
       
  destruct (pred_task_term_occur r (reducer r (remaining_sprop r0 xs0 P rs))) eqn: E.
      - constructor. 
        * apply prop_sub_get_pred_sub_keep_pred_legal. rew. apply prop_sub_get_pred_sub_keep_pred_legal. apply IHQ1; try easy.
           intros. apply H3 in H6. zero_r H6.
        * rew. clear IHQ1. specialize IHQ2 with r0 xs0 P (r::rs) (None::us)(length xs::ns) args. simpl in IHQ2. 
           apply IHQ2 in H11; try easy; try now f_equal.  
           ++ constructor. easy. rewrite reducer_app.  rewrite pred_task_term_occur_app. now rewrite H5.  
           ++  intros. destruct H6; try discriminate. apply H3 in H6. zero_r H6. 
      - remember (newr (upred r:: prop_ustr Q2 ++ task_ustr (reducer r (renaming_pred_task rs us) ++
            reducer r (remaining_sprop r0 xs0 P rs)))) as z. constructor.
            * apply prop_sub_get_pred_sub_keep_pred_legal. rew. apply prop_sub_get_pred_sub_keep_pred_legal. apply IHQ1; try easy.
                intros. apply H3 in H6. zero_r H6.
            * rew. clear IHQ1.  specialize IHQ2 with r0 xs0 P (r::rs) (Some z::us)(length xs::ns) args. simpl in IHQ2. 
                apply IHQ2 in H11; try now f_equal.  
               ++ constructor. easy. pred_notin. pred_notin.  
               ++ intros. destruct H6. injection H6 as H6. subst x. pred_notin. apply H3 in H6. zero_r H6.              
Qed.
        
Corollary preddef_unfold_keep_pred_legal: forall Q r xs P args,
  pred_legal [[ let r xs := P in Q ]] args ->
  pred_legal (prop_sub [sprop r xs P] Q) args.
Proof.
  intros. inversion H; subst. pose proof preddef_unfold_keep_pred_legal_lemma Q r xs P nil nil nil.
  simpl in H0. apply H0; auto. constructor. intros. now exfalso.
Qed.

Corollary preddef_unfold_keep_legal: forall r xs P Q,
  legal [[ let r xs := P in Q ]]  ->
  legal (prop_sub [sprop r xs P] Q).
Proof. intros. inversion H; subst. now apply preddef_unfold_keep_pred_legal. Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*              Other Lemmas about prop_sub           *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Lemma get_pred_sub_keep_extend_pred_naive_iff: forall r st ts1 ts2,
  naive (extend_pred r ts1 st) <->
  naive (extend_pred r ts2 (get_pred_sub st)).
Proof.
  induction st; intros.
  + simpl. split; intros; inversion H.
  + split; intros.
      - destruct a.
        * simpl in H. simpl. eapply IHst. eauto.
        * simpl in *. cname. inversion H. eapply IHst. eauto. 
        * simpl in *. cname. apply instantiate_var_binder_keep_naive_iff.
           now apply instantiate_var_binder_keep_naive_iff in H. eapply IHst. eauto.
      - destruct a.
         * simpl in*. rewrite <- IHst in H. eauto.
         * simpl in *. cname. inversion H. rewrite IHst. eauto.
         * simpl in *. cname.  apply instantiate_var_binder_keep_naive_iff.
           now apply instantiate_var_binder_keep_naive_iff in H.  rewrite IHst. eauto.
Qed.
          

Lemma get_pred_sub_keep_atom_sub_aux_naive_iff: forall a st ts1 ts2,
  naive (atom_sub_aux a ts1 st) <->
  naive (atom_sub_aux a ts2 (get_pred_sub st)).
Proof.
  induction a.  intros.
  + apply get_pred_sub_keep_extend_pred_naive_iff.
  + split;intros; simpl in *. 
      - rewrite<- IHa. eauto.
      - rewrite IHa. eauto.
Qed. 

Lemma get_pred_sub_keep_prop_sub_naive_iff: forall  P st,
  naive (prop_sub st P) <->
  naive (prop_sub (get_pred_sub st) P).
Proof.
   induction P; intros; simpl; split; intros;try constructor; simpl in H;[idtac|idtac|inversion H; subst;try eapply IHP; 
    try eapply IHP1; try eapply IHP2; eauto; try now repeat rewrite <- IHP;  try now repeat rewrite <- IHP1
    ;  try now repeat rewrite <- IHP2..
    | idtac|idtac|idtac| idtac|idtac|idtac].
    + unfold atom_sub. erewrite <- get_pred_sub_keep_atom_sub_aux_naive_iff. eauto. 
    + unfold atom_sub. erewrite get_pred_sub_keep_atom_sub_aux_naive_iff. eauto.
    + destruct (task_term_occur x (reducev x st)); destruct (task_term_occur x (reducev x (get_pred_sub st))); constructor; 
        inversion H; subst.
        * rewrite <- get_pred_sub_reducev_swap. now rewrite <- IHP. 
        * apply IHP. simpl. rewrite <- get_pred_sub_reducev_swap. 
            rewrite no_var_sub_get_pred_sub.  now rewrite <- IHP. 
            apply get_pred_sub_no_var_sub.
        * rewrite <- get_pred_sub_reducev_swap. apply IHP in H1. now simpl in H1. 
        * apply IHP. simpl. rewrite <- get_pred_sub_reducev_swap. 
            apply IHP in H1. simpl in H1.  rewrite no_var_sub_get_pred_sub. easy.  
            apply get_pred_sub_no_var_sub.
    + destruct (task_term_occur x (reducev x st)); destruct (task_term_occur x (reducev x (get_pred_sub st))); constructor; 
        inversion H; subst.
        * rewrite  <- get_pred_sub_reducev_swap in H1. now rewrite IHP. 
        * apply IHP. apply IHP in H1. simpl in H1.
           rewrite <- get_pred_sub_reducev_swap in H1.   rewrite no_var_sub_get_pred_sub in H1; try easy. 
            apply get_pred_sub_no_var_sub.
        * rewrite  <- get_pred_sub_reducev_swap in H1. now rewrite IHP. 
        * apply IHP. simpl. apply IHP in H1. simpl in H1.
           rewrite <- get_pred_sub_reducev_swap in H1.   rewrite no_var_sub_get_pred_sub in H1; try easy. 
           apply get_pred_sub_no_var_sub.
     + destruct (task_term_occur x (reducev x st)); destruct (task_term_occur x (reducev x (get_pred_sub st))); constructor; 
        inversion H; subst.
        * rewrite <- get_pred_sub_reducev_swap. now rewrite <- IHP. 
        * apply IHP. simpl. rewrite <- get_pred_sub_reducev_swap. 
            rewrite no_var_sub_get_pred_sub.  now rewrite <- IHP. 
            apply get_pred_sub_no_var_sub.
        * rewrite <- get_pred_sub_reducev_swap. apply IHP in H1. now simpl in H1. 
        * apply IHP. simpl. rewrite <- get_pred_sub_reducev_swap. 
            apply IHP in H1. simpl in H1.  rewrite no_var_sub_get_pred_sub. easy.  
            apply get_pred_sub_no_var_sub.
    + destruct (task_term_occur x (reducev x st)); destruct (task_term_occur x (reducev x (get_pred_sub st))); constructor; 
        inversion H; subst.
        * rewrite  <- get_pred_sub_reducev_swap in H1. now rewrite IHP. 
        * apply IHP. apply IHP in H1. simpl in H1.
           rewrite <- get_pred_sub_reducev_swap in H1.   rewrite no_var_sub_get_pred_sub in H1; try easy. 
            apply get_pred_sub_no_var_sub.
        * rewrite  <- get_pred_sub_reducev_swap in H1. now rewrite IHP. 
        * apply IHP. simpl. apply IHP in H1. simpl in H1.
           rewrite <- get_pred_sub_reducev_swap in H1.   rewrite no_var_sub_get_pred_sub in H1; try easy. 
           apply get_pred_sub_no_var_sub.
     + rewrite <- get_pred_sub_reducer_swap. rewrite pred_task_term_occur_get_pred_sub.
        destruct (pred_task_term_occur r (reducer r st)); inversion H.
     + rewrite <- get_pred_sub_reducer_swap in H. rewrite pred_task_term_occur_get_pred_sub in H.
        destruct (pred_task_term_occur r (reducer r st)); inversion H.
Qed.

Lemma atom_sub_aux_naive: forall r xs P a ts,
  atom_pred a = r ->
  naive P ->
  naive (atom_sub_aux a ts [sprop r xs P]).
Proof.
  induction a; intros.
  + simpl in H. subst r0. simpl. cname. now apply instantiate_var_binder_keep_naive_iff.
  + simpl. now apply IHa.
Qed.

Lemma preddef_unfold_naive: forall r xs P Q,
  legal [[let r xs := P in Q]] ->
  closed [[let r xs:= P in Q]] ->
  naive P ->
  atom_naive Q ->
  naive (prop_sub [sprop r xs P] Q).
Proof.
  intros. inversion H; subst. clear H. hnf in H0. simpl in H0. 
  induction H2; intros; simpl; try constructor; try apply IHatom_naive; try apply IHatom_naive1; try apply IHatom_naive2; try easy;
  try now inversion H9; try (intro r0; specialize H0 with r0; cname; zero_r H0; zero_r H; now rewrite H0).
  + simpl in H9. inversion H9; subst. simpl in H2. destruct (R.eq_dec (atom_pred a) r).
      - now apply atom_sub_aux_naive.
      - specialize H0 with (atom_pred a). cname. zero_r H0. rewrite atom_pred_pred_atom_occur in H. discriminate.
  + destruct ((if in_vars x xs then 0 else free_occur x P) + 0 ).
      - simpl. constructor. apply IHatom_naive. easy. now inversion H9.
      - simpl. constructor. apply get_pred_sub_keep_prop_sub_naive_iff.
        simpl.  apply IHatom_naive. easy. now inversion H9.
   + destruct ((if in_vars x xs then 0 else free_occur x P) + 0 ).
      - simpl. constructor. apply IHatom_naive. easy. now inversion H9.
      - simpl. constructor. apply get_pred_sub_keep_prop_sub_naive_iff.
        simpl.  apply IHatom_naive. easy. now inversion H9. 
Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*              Lemmas link prop_sub and beta_reduction              *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)


Ltac test_bstar:= LAM.check_bstar; try apply rt_refl.

Fixpoint add_app(a:LAM.tm)(ts: list LAM.tm):=
  match ts with
  | nil => a
  | t::ts0 => add_app (LAM.app a t) ts0
end.

Lemma add_app_bstar: forall t1 t2 ts,
  LAM.bstar t1 t2 ->
  LAM.bstar (add_app t1 ts) (add_app t2 ts).
Proof.
  intros. revert t1 t2 H. induction ts; intros.
  + easy.
  + simpl. apply IHts. test_bstar.
Qed.

Lemma construct_atom_atom2tm: forall a ts,
  atom2tm (construct_atom a ts) = add_app (atom2tm a) (map term2tm ts).
Proof.
  intros. revert a. induction ts; intros.
  + easy.
  + simpl. now rewrite IHts.
Qed.

Lemma add_app_subst: forall a ts st,
  LAM.subst st (add_app a ts) = add_app (LAM.subst st a) (map (LAM.subst st) ts).
Proof.
  intros. revert a st. induction ts; intros.
  + easy.
  + simpl. now rewrite IHts.
Qed. 

Lemma instantiate_var_binder_bstar: forall P xs ts,
  length xs = length ts ->
  LAM.bstar (add_app (tm_add_binders xs (prop2tm P)) (map term2tm ts)) (prop2tm (instantiate_var_binder P xs ts)).
Proof.
  intros. revert P xs H. induction ts; intros; destruct xs; try inversion H.
  + test_bstar.
  + simpl. econstructor 3. apply add_app_bstar. repeat constructor.
      rename t into x. rename a into t.
      pose proof tm_add_binders_subst xs [(svar x t)] P.
      simpl in H0. assert (forall x y z, x = y -> LAM.bstar x z -> LAM.bstar y z) by congruence. eapply H2. 
      assert (forall x y ts, x = y -> add_app x ts = add_app y ts) by congruence. eapply H3. 
      symmetry. apply H0. clear H2. rewrite <- prop_var_sub_FOL_LAM. apply IHts.
      rewrite <- H1. apply vars_new_xs_length. apply vars_new_st_only_var_sub. repeat constructor. 
Qed.

Lemma extend_pred_bstar: forall r ts st,
  atom_legal (construct_atom (APred r) ts) (subst_task_to_pred_args st)->
  LAM.bstar  (add_app (LAM.subst (st_FOL2LAM st) (LAM.var (upred r))) (map term2tm ts))
  (prop2tm (extend_pred r ts st)).
Proof.
  intros. revert r ts H. induction st; intros.
  + simpl. rewrite construct_atom_atom2tm. test_bstar.
  + destruct a.
      - simpl. cname. apply IHst. simpl in H. easy.
      - simpl. cname.
        * simpl. rewrite construct_atom_atom2tm. test_bstar.
        * apply IHst. now simpl in H. 
      - simpl. simpl in H. rewrite construct_atom_pred in H.  simpl in H. cname.
        * apply instantiate_var_binder_bstar. now rewrite construct_atom_length in H. 
        * now apply IHst. 
Qed.

Lemma map_term_sub: forall st ts,
  map (LAM.subst (st_FOL2LAM st)) (map term2tm ts) = map term2tm (map (term_sub st) ts).
Proof.
  induction ts.
  + easy.
  + simpl. rewrite IHts. now rewrite term_sub_FOL_LAM.
Qed. 
   
Lemma app_add_app: forall a t ts,
  add_app (LAM.app a t) ts = add_app a (t::ts).
Proof. easy. Qed.
   
Lemma atom_sub_aux_bstar: forall st a ts,
  atom_legal (construct_atom a ts) (subst_task_to_pred_args st) ->
  LAM.bstar (LAM.subst (st_FOL2LAM st)(atom2tm (construct_atom a ts)))
  (prop2tm (atom_sub_aux a (map (term_sub st) ts) st)).
Proof.
  intros. rewrite construct_atom_atom2tm. rewrite add_app_subst. revert st ts H.
  induction a; intros.
  + simpl. rewrite map_term_sub. apply extend_pred_bstar. 
      apply construct_atom_legal_length with ts. now rewrite map_length. easy.
  + simpl. rewrite app_add_app. repeat rewrite <- map_cons. now apply IHa. 
Qed.

Corollary atom_sub_bstar: forall a st,
  atom_legal a (subst_task_to_pred_args st) ->
  LAM.bstar (LAM.subst (st_FOL2LAM st) (atom2tm a))  (prop2tm (atom_sub st a)).
Proof. intros. now apply atom_sub_aux_bstar with (ts:=nil). Qed.       

Lemma vars_new_st_subst_task_to_pred_args: forall xs d st,
  subst_task_to_pred_args (vars_new_st d xs st) = subst_task_to_pred_args st.
Proof.
  induction xs; intros.
  + easy.
  + simpl.  destruct (task_term_occur a (reducev a st)).
      - rewrite IHxs. apply reducev_subst_task_to_pred_args.
      - rewrite IHxs. simpl. apply reducev_subst_task_to_pred_args.
Qed. 

Lemma prop_sub_bstar: forall st P,
  pred_legal P (subst_task_to_pred_args st) ->
  LAM.bstar (LAM.subst (st_FOL2LAM st) (prop2tm P)) (prop2tm (prop_sub st P)).
Proof.
  intros. revert st H. induction P; intros.
  + simpl. FOL2LAM. test_bstar.
  + simpl. FOL2LAM. test_bstar.
  + simpl. inversion H; subst. clear H. now apply atom_sub_bstar.
  + simpl. test_bstar.
  + simpl. test_bstar. 
  + simpl. test_bstar. apply IHP. now inversion H.
  + simpl. inversion H; subst. test_bstar; auto.
  + simpl. inversion H; subst. test_bstar; auto.
  + simpl. inversion H; subst. test_bstar; auto.
  + simpl. inversion H; subst. test_bstar; auto.
  + simpl. LAM2FOL. destruct (task_term_occur x (reducev x st)).
      - simpl. test_bstar. apply IHP. inversion H; subst. auto. now rewrite reducev_subst_task_to_pred_args.
      - simpl. rewrite newv_FOL_LAM. simpl. FOL2LAM. test_bstar. apply LAM.bstar_abs. 
        remember (V.list_new_name (x :: variable_list
                 (LAM.tm_var (prop2tm P) ++
                  LAM.task_var (LAM.reduce x (st_FOL2LAM st))))) as z.
        specialize IHP with ((svar x z)::(reducev x st)). simpl in IHP. subst z. LAM2FOL.  apply IHP.
        inversion H; subst. now rewrite reducev_subst_task_to_pred_args.
  + simpl. LAM2FOL.  destruct (task_term_occur x (reducev x st)).
      - simpl. test_bstar. apply IHP. inversion H; subst. auto. now rewrite reducev_subst_task_to_pred_args.
      - simpl. rewrite newv_FOL_LAM. simpl. FOL2LAM. test_bstar. apply LAM.bstar_abs. 
        remember (V.list_new_name (x :: variable_list
                 (LAM.tm_var (prop2tm P) ++
                  LAM.task_var (LAM.reduce x (st_FOL2LAM st))))) as z.
        specialize IHP with ((svar x z)::(reducev x st)). simpl in IHP. subst z. LAM2FOL. apply IHP.
        inversion H; subst. now rewrite reducev_subst_task_to_pred_args.
  + simpl. cname. LAM2FOL. destruct (pred_task_term_occur r (reducer r st)).
      - simpl. test_bstar. apply IHP2.  inversion H; subst. rewrite reducer_subst_task_to_pred_args.
         apply reduce_arg_pred_legal with (r:=r) in H6. simpl in H6. cname.
         now rewrite reduce_arg_reduce_arg in H6. 
         rewrite tm_add_binders_subst. apply tm_add_binders_bstar. apply IHP1.
         inversion H; subst. now rewrite vars_new_st_subst_task_to_pred_args. 
      - simpl. repeat rewrite newr_FOL_LAM. FOL2LAM. simpl. test_bstar.
         * apply LAM.bstar_abs. remember (R.list_new_name
            (r:: predname_list (LAM.tm_var (prop2tm P2) ++
            LAM.task_var (LAM.reduce (upred r) (st_FOL2LAM st))))) as z.
            LAM2FOL. specialize IHP2 with ((spred r z)::(reducer r st)). subst z.
            simpl in IHP2. apply IHP2. inversion H; subst. apply reduce_arg_pred_legal with (r:=r) in H6.
            simpl in H6. cname.   rewrite reduce_arg_reduce_arg in H6.
            now rewrite reducer_subst_task_to_pred_args. 
         * rewrite tm_add_binders_subst. apply tm_add_binders_bstar. apply IHP1.
            inversion H; subst. now rewrite vars_new_st_subst_task_to_pred_args. 
Qed.  

Lemma preddef_unfold_bstar_lemma: forall r xs P Q,
  LAM.bstar (prop2tm [[let r xs:= P in Q]]) (LAM.subst (st_FOL2LAM [(sprop r xs P)]) (prop2tm Q)).
Proof. intros. simpl. econstructor 3. repeat constructor. test_bstar. Qed.  

(** Unfold one preddef is beta_reduction **)
Corollary preddef_unfold_bstar: forall r xs  P Q,
  legal [[let r xs := P in Q]] ->
  LAM.bstar  (prop2tm [[let r xs:= P in Q]])  (prop2tm (prop_sub [(sprop r xs P)] Q)).
Proof. 
  intros. econstructor 3. 
  apply preddef_unfold_bstar_lemma. 
  apply prop_sub_bstar. 
  now inversion H.
Qed.

(*** Lemmas about beta normal form ***)
Lemma term2tm_not_abs: forall t,
  LAM.not_abs (term2tm t).
Proof. destruct t; simpl; constructor. Qed.

Ltac test_bnf:= LAM.check_bnf; try apply term2tm_not_abs; try tauto.

Lemma term2tm_bnf: forall t:term,
  LAM.beta_normal_form (term2tm t).
Proof. induction t; intros; simpl; test_bnf. Qed.

Lemma atom2tm_not_abs: forall a,
  LAM.not_abs (atom2tm a).
Proof. destruct a; simpl; constructor. Qed.

Lemma prop2tm_not_abs: forall P,
  LAM.not_abs (prop2tm P).
Proof. destruct P; simpl; try apply atom2tm_not_abs; constructor.  Qed.

Lemma naive_prop2tm_bnf: forall P,
  naive P ->
  LAM.beta_normal_form (prop2tm P).
Proof. intros. induction H; simpl; test_bnf; try apply term2tm_bnf; apply prop2tm_not_abs. Qed.

Lemma bstar_congruence_l: forall x y z,
  x = y ->
  LAM.bstar x z ->
  LAM.bstar y z.
Proof. intros. subst y. easy. Qed.

Lemma beta_congruence_r: forall x y z,
  y = z ->
  LAM.beta_reduction x y ->
  LAM.beta_reduction x z.
Proof. intros. subst y. easy. Qed.


(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*      Eliminate all predicates in layer_form propositions              *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)
Inductive layer_form: prop -> Prop:=
  | atom_naive_lf: forall P,
        atom_naive P ->
        layer_form P
  | PPreddef_lf: forall r xs P Q,
        atom_naive P ->
        layer_form Q ->
        layer_form [[let r xs := P in Q]]
.

Fixpoint layer_formb (p:prop):bool:=
  match p with
  | PPredDef r xs P Q => atom_naiveb P && layer_formb Q
  | _ => atom_naiveb p
  end.
  
Lemma layer_form_layer_formb: forall P,
  layer_form P <-> layer_formb P = true.
Proof.
  split.
  + intros. induction H; intros. 
      - induction H; intros; try reflexivity; simpl; try apply andb_true_iff; try split; try now apply atom_naive_atom_naiveb.
      - simpl. apply atom_naive_atom_naiveb in H. now apply andb_true_iff.
  + induction P; intros; [repeat constructor; simpl in H; try apply andb_true_iff in H; try now apply atom_naive_atom_naiveb..
  |  simpl in H; apply andb_true_iff in H; constructor 2;[apply atom_naive_atom_naiveb|]; tauto]. 
Qed.  

Lemma prop_sub_lf: forall P st,
  Forall sprop_atom_naive st ->
  layer_form P ->
  layer_form (prop_sub st P).
Proof.
  induction P; intros; inversion H0; subst;[constructor; now apply prop_sub_atom_naive..|]. 
  + simpl. destruct (pred_task_term_occur r (reducer r st)).
      - constructor 2. apply prop_sub_atom_naive. 
        now apply vars_new_st_sprop_atom_naive. 
        easy. apply IHP2. now apply reducer_Forall. easy.
      - constructor 2. apply prop_sub_atom_naive. 
        now apply vars_new_st_sprop_atom_naive.
        easy. apply IHP2. apply Forall_cons. exact I. 
        now apply reducer_Forall. easy.
Qed.
  
Fixpoint preddef_num_lf (d:prop):nat:=
  match d with
  | [[let r xs:= P in Q]] => S (preddef_num_lf Q)
  | _ => O
 end.
 
Fixpoint preddef_elim_lf_aux (d:prop)(n:nat):prop:=
   match n, d with
   | S n', [[let r xs:= P in Q]] => preddef_elim_lf_aux (prop_sub [(sprop r xs P)] Q) n'
   | _ , _ => d
   end.
   
Definition preddef_elim_lf (d:prop):=
  preddef_elim_lf_aux d (preddef_num_lf d).

Corollary preddef_unfold_keep_layer_form: forall r xs P Q,
  layer_form [[let r xs:= P in Q]] ->
  layer_form  (prop_sub [(sprop r xs P)] Q).
Proof.
  intros. inversion H; subst. inversion H0. 
  apply prop_sub_lf; try easy; repeat constructor; easy.
Qed.

Lemma preddef_elim_lf_aux_bstar: forall P n,
  legal P ->
  LAM.bstar (prop2tm P) (prop2tm (preddef_elim_lf_aux P n)).
Proof.
  intros. revert P H. induction n; intros.
  + test_bstar.
  + simpl. destruct P ;[test_bstar..|idtac]. econstructor 3.
     now apply preddef_unfold_bstar. apply IHn.
     now apply preddef_unfold_keep_legal. 
Qed. 

Theorem preddef_elim_lf_bstar: forall P,
  legal P ->  LAM.bstar (prop2tm P) (prop2tm (preddef_elim_lf P)).
Proof. intros. now apply preddef_elim_lf_aux_bstar. Qed.

Lemma layer_form_with_preddef_num_zero_is_atom_naive: forall P,
  layer_form P ->
  preddef_num_lf P = 0 <-> atom_naive P.
Proof.
  intros. split.
  + induction H; intros.
      - easy.
      - inversion H1.
  + induction H; intros.
     - induction H; simpl; try rewrite IHP; try rewrite IHP1; try rewrite IHP2; easy.
     - inversion H1.
Qed.

Lemma sprop_atom_naive_same_preddef_num_lf: forall P st,
  layer_form P ->
  Forall sprop_atom_naive st ->
  preddef_num_lf P = preddef_num_lf (prop_sub st P).
Proof.
  intros. revert st H0. induction H; intros.
  + assert (preddef_num_lf P = 0). 
      apply layer_form_with_preddef_num_zero_is_atom_naive. 
      now constructor. easy. rewrite H1. 
      assert (atom_naive (prop_sub st P)).
      now apply prop_sub_atom_naive.
      assert (preddef_num_lf (prop_sub st P)= 0).
      apply layer_form_with_preddef_num_zero_is_atom_naive. 
      now constructor. easy. congruence.
  + simpl. destruct (pred_task_term_occur r (reducer r st)).
      - simpl. f_equal. apply IHlayer_form. now apply reducer_Forall.
      - simpl. f_equal. apply IHlayer_form. apply Forall_cons.
        easy. now apply reducer_Forall.
Qed.

Lemma preddef_elim_lf_aux_naive: forall n P,
  closed P ->
  legal P ->
  layer_form P ->
  preddef_num_lf P = n ->
  naive (preddef_elim_lf_aux P n).
Proof.
  induction n; intros.
  + rewrite layer_form_with_preddef_num_zero_is_atom_naive in H2. 2:easy. simpl. 
      now apply closed_atom_naive_is_naive.
  + inversion H1; subst.
      - rewrite <- layer_form_with_preddef_num_zero_is_atom_naive in H3. 
        rewrite H2 in H3. discriminate. easy.
      - simpl. apply IHn. now apply preddef_unfold_keep_closed.
         now apply preddef_unfold_keep_legal. 
         now apply preddef_unfold_keep_layer_form.
         simpl in H2. injection H2 as H2.  
         rewrite <- sprop_atom_naive_same_preddef_num_lf; try easy.
         constructor. easy. constructor.
Qed.
  
Lemma preddef_elim_lf_aux_atom_naive: forall n P,
  legal P ->
  layer_form P ->
  preddef_num_lf P = n ->
  atom_naive (preddef_elim_lf_aux P n).
Proof.
  induction n; intros.
  + rewrite layer_form_with_preddef_num_zero_is_atom_naive in H1. 2:easy. now simpl. 
  + inversion H0; subst.
      - rewrite <- layer_form_with_preddef_num_zero_is_atom_naive in H2. 
        rewrite H2 in H1. discriminate. easy.
      - simpl. apply IHn. 
         now apply preddef_unfold_keep_legal. 
         now apply preddef_unfold_keep_layer_form.
         simpl in H1. injection H1 as H1.  
         rewrite <- sprop_atom_naive_same_preddef_num_lf; try easy.
         constructor. easy. constructor.
Qed.  

(* Definition good_lf(P:prop):= 
  closed P /\ legal P /\ layer_form P.
  
Definition good_lfb (P:prop):=
  layer_formb P && legalb P && closedb P.
  
Corollary good_lf_good_lfb: forall P,
  good_lf P <->  good_lfb P = true.
Proof.
  unfold good_lf. unfold good_lfb. split; intros. 
  + destruct H as [? [? ?] ].
      apply closed_closedb in H.
      apply legal_legalb in H0.
      apply layer_form_layer_formb in H1.
      rewrite H. rewrite H0. rewrite H1. easy.
  + apply andb_prop in H. destruct H. 
      apply andb_prop in H. destruct H. 
      split; [|split].  
      - now apply closed_closedb.
      - now apply legal_legalb.
      - now apply layer_form_layer_formb.
Qed.     
 *)

Theorem preddef_elim_lf_naive: forall P,
  closed P ->
  legal P ->
  layer_form P ->
  naive (preddef_elim_lf P).
Proof. intros. apply preddef_elim_lf_aux_naive; tauto. Qed. 

Theorem preddef_elim_lf_atom_naive: forall P,
  legal P ->
  layer_form P ->
  atom_naive (preddef_elim_lf P).
Proof. intros. apply preddef_elim_lf_aux_atom_naive; tauto. Qed.

Lemma prop_var_sub_keep_layer_form: forall P st,
  layer_form P ->
  layer_form (prop_var_sub st P).
Proof.
  intros. revert st. induction H; intros.
  + constructor. now apply prop_var_sub_keep_atom_naive.
  + simpl. destruct (pred_task_term_occur r (reducer r st)).
      - constructor 2. now apply prop_var_sub_keep_atom_naive. apply IHlayer_form.
      - constructor 2. now apply prop_var_sub_keep_atom_naive. apply IHlayer_form. 
Qed.
  
(* Lemma naive_is_good_lf: forall P, 
  naive P -> good_lf P.
Proof.
  intros. unfold good_lf. split; [| split].
  + unfold closed. intros. now apply naive_no_pred.
  + now apply naive_legal.
  + constructor. now apply naive_is_atom_naive.
Qed. *)

Lemma preddef_elim_lf_aux_keep_no_pred_free_occur: forall r n P,
  pred_free_occur r P = 0 ->
  pred_free_occur r (preddef_elim_lf_aux P n) = 0.
Proof.
  induction n; intros.
  + easy.
  + simpl. destruct P; try easy. 
      apply preddef_unfold_keep_no_pred_free_occur in H. auto.
Qed.

Corollary preddef_elim_lf_keep_no_pred_free_occur: forall r P,
  pred_free_occur r P = 0 ->
  pred_free_occur r (preddef_elim_lf P) = 0.
Proof. intros. now apply preddef_elim_lf_aux_keep_no_pred_free_occur. Qed.

Corollary preddef_elim_lf_keep_closed: forall P,
  closed P -> closed (preddef_elim_lf P).
Proof.
  intros. hnf in *. intros. 
  apply preddef_elim_lf_keep_no_pred_free_occur. auto.
Qed. 

Lemma preddef_elim_lf_aux_keep_pred_legal: forall n P args,
  pred_legal P args ->
  pred_legal (preddef_elim_lf_aux P n) args.
Proof.
  induction n; intros.
  + easy.
  + simpl. destruct P; try easy. 
      apply preddef_unfold_keep_pred_legal in H. auto.
Qed.

Corollary preddef_elim_lf_keep_pred_legal: forall P args,
  pred_legal P args ->
  pred_legal (preddef_elim_lf P) args.
Proof. intros. now apply preddef_elim_lf_aux_keep_pred_legal. Qed.

Corollary preddef_elim_lf_keep_legal: forall P,
  legal P  ->
  legal (preddef_elim_lf P).
Proof. intros. now apply preddef_elim_lf_aux_keep_pred_legal. Qed.

(* Lemma PImpl_layer_form_atom_naive: forall P Q,
  layer_form [[P -> Q]] -> atom_naive P /\ atom_naive Q.
Proof. intros.  intros. inversion H; subst. now inversion H0. Qed.

Lemma PAnd_layer_form_atom_naive: forall P Q,
  layer_form [[P /\ Q]] -> atom_naive P /\ atom_naive Q.
Proof. intros.  intros. inversion H; subst. now inversion H0. Qed.

Lemma POr_layer_form_atom_naive: forall P Q,
  layer_form [[P \/ Q]] -> atom_naive P /\ atom_naive Q.
Proof. intros.  intros. inversion H; subst. now inversion H0. Qed.

Lemma PIff_layer_form_atom_naive: forall P Q,
  layer_form [[P -> Q]] -> atom_naive P /\ atom_naive Q.
Proof. intros.  intros. inversion H; subst. now inversion H0. Qed.

Lemma PNot_layer_form_atom_naive: forall P,
  layer_form [[¬ P]] -> atom_naive P.
Proof. intros.  intros. inversion H; subst. now inversion H0. Qed.

Lemma PForall_layer_form_atom_naive: forall x P,
  layer_form [[∀ x, P]] -> atom_naive P.
Proof. intros.  intros. inversion H; subst. now inversion H0. Qed.

Lemma PExists_layer_form_atom_naive: forall x P,
  layer_form [[∃ x, P]] -> atom_naive P.
Proof. intros.  intros. inversion H; subst. now inversion H0. Qed.
 *)

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*      Eliminate all predicates in simple_preddef_form propositions              *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Inductive combined_layer_form: prop -> Prop :=
   | layer_form_clf: forall P,
        layer_form P -> combined_layer_form P
   | PNot_clf: forall P,
        combined_layer_form P -> combined_layer_form (PNot P)
   | PAnd_clf: forall P Q,
        combined_layer_form P -> 
        combined_layer_form Q ->
        combined_layer_form (PAnd P Q)
    | POr_clf: forall P Q,
        combined_layer_form P -> 
        combined_layer_form Q ->
        combined_layer_form (POr P Q)
    | PImpl_clf: forall P Q,
        combined_layer_form P -> 
        combined_layer_form Q ->
        combined_layer_form (PImpl P Q)
    | PIff_clf: forall P Q,
        combined_layer_form P -> 
        combined_layer_form Q ->
        combined_layer_form (PIff P Q)
    | PForall_clf: forall x P,
        combined_layer_form P -> combined_layer_form (PForall x P)
    | PExists_clf: forall x P,
        combined_layer_form P -> combined_layer_form (PExists x P)
    | PPredDef_clf: forall r xs P Q,
        atom_naive P ->
        combined_layer_form Q ->
        combined_layer_form (PPredDef r xs P Q)
.

Inductive simpl_preddef_form: prop -> Prop:=
  | PEq_spf: forall t1 t2,
      simpl_preddef_form (PEq t1 t2)
  | PRel_spf: forall t1 t2,
      simpl_preddef_form (PRel t1 t2)
  | PAtom_spf: forall a,
      simpl_preddef_form (PAtom a)
  | PTrue_spf:  simpl_preddef_form PTrue
  | PFalse_spf:  simpl_preddef_form PFalse
  | PNot_spf: forall P,
      simpl_preddef_form P ->
      simpl_preddef_form (PNot P)
  | PAnd_spf: forall P Q,
      simpl_preddef_form P ->
      simpl_preddef_form Q ->
      simpl_preddef_form (PAnd P Q)
  | POr_spf: forall P Q,
      simpl_preddef_form P ->
      simpl_preddef_form Q ->
      simpl_preddef_form (POr P Q)
  | PImpl_spf: forall P Q,
      simpl_preddef_form P ->
      simpl_preddef_form Q ->
      simpl_preddef_form (PImpl P Q)
  | PIff_spf: forall P Q,
      simpl_preddef_form P ->
      simpl_preddef_form Q ->
      simpl_preddef_form (PIff P Q)
  | PForall_spf: forall x P,
      simpl_preddef_form P ->
      simpl_preddef_form (PForall x P)
  | PExists_spf: forall x P,
      simpl_preddef_form P ->
      simpl_preddef_form (PExists x P)
  | PPredDef_spf: forall r xs P Q,
      atom_naive P ->
      simpl_preddef_form Q ->
      simpl_preddef_form (PPredDef r xs P Q)
.    
      
Lemma combined_layer_form_simpl_preddef_form_eq: forall P,
  combined_layer_form P <-> simpl_preddef_form P.
Proof.
  split; intros.
  + induction H; try now constructor. 
      induction H; try now constructor.
      induction H; now constructor.
  + revert H. induction P; intros.
      - repeat constructor.
      - repeat constructor.
      - repeat constructor.
      - repeat constructor.
      - repeat constructor.
      - apply PNot_clf. inversion H; subst. tauto.
      - inversion H; subst. apply PAnd_clf; tauto.
      - inversion H; subst. apply POr_clf; tauto.
      - inversion H; subst. apply PImpl_clf; tauto.
      - inversion H; subst. apply PIff_clf; tauto.
      - inversion H; subst. apply PForall_clf; tauto.
      - inversion H; subst. apply PExists_clf; tauto.
      - inversion H; subst. apply PPredDef_clf; tauto.
Qed.
  
Fixpoint simpl_preddef_formb (p:prop): bool:=
  match p with
  | PNot P => simpl_preddef_formb P
  | PAnd P Q
  | POr P Q
  | PImpl P Q
  | PIff P Q => simpl_preddef_formb P && simpl_preddef_formb Q
  | PForall x P 
  | PExists x P =>  simpl_preddef_formb P
  | PPredDef r xs P Q  => atom_naiveb P && simpl_preddef_formb Q
  | _ => true
  end.
  
Lemma simpl_preddef_form_simpl_preddef_formb: forall P,
  simpl_preddef_form P <-> simpl_preddef_formb P = true.
Proof.
  split; intros.
  + induction H; simpl; try rewrite IHP; try rewrite IHsimpl_preddef_form1; try rewrite IHsimpl_preddef_form2; try easy.
      rewrite atom_naive_atom_naiveb in H. rewrite H. rewrite IHsimpl_preddef_form. easy.
  + induction P; intros; simpl in H; try (apply andb_true_iff in H; destruct H); try constructor; try tauto.
      now apply atom_naive_atom_naiveb.
Qed.

Corollary combined_layer_form_simpl_preddef_formb: forall P,
  combined_layer_form P <-> simpl_preddef_formb P = true.
Proof.
   split; intros.
   + apply simpl_preddef_form_simpl_preddef_formb. now apply combined_layer_form_simpl_preddef_form_eq.
   + apply combined_layer_form_simpl_preddef_form_eq. now apply simpl_preddef_form_simpl_preddef_formb.
Qed.
  
Fixpoint preddef_elim_clf (p:prop): prop:=
  match layer_formb p with
  | true => preddef_elim_lf p
  | false => 
        match p with
         | PNot P => PNot (preddef_elim_clf P)
         | PAnd P1 P2 => PAnd (preddef_elim_clf P1) (preddef_elim_clf P2)
         | POr P1 P2 => POr (preddef_elim_clf P1) (preddef_elim_clf P2)
         | PImpl P1 P2 => PImpl (preddef_elim_clf P1) (preddef_elim_clf P2)
         | PIff P1 P2 => PIff (preddef_elim_clf P1) (preddef_elim_clf P2)
         | PForall x P => PForall x (preddef_elim_clf P)
         | PExists x P => PExists x (preddef_elim_clf P)
         | PPredDef r xs P Q => 
                let Q':= preddef_elim_clf Q in  
                    prop_sub [(sprop r xs P)] Q'
         | _ => p
         end
  end.

Lemma preddef_elim_clf_unfold_one_iteration: forall p,
  preddef_elim_clf p = match layer_formb p with
                                  | true => preddef_elim_lf p
                                  | false =>  match p with
                                  | PNot P => PNot (preddef_elim_clf P)
                                  | PAnd P1 P2 => PAnd (preddef_elim_clf P1) (preddef_elim_clf P2)
                                  | POr P1 P2 => POr (preddef_elim_clf P1) (preddef_elim_clf P2)
                                  | PImpl P1 P2 => PImpl (preddef_elim_clf P1) (preddef_elim_clf P2)
                                  | PIff P1 P2 => PIff (preddef_elim_clf P1) (preddef_elim_clf P2)
                                  | PForall x P => PForall x (preddef_elim_clf P)
                                  | PExists x P => PExists x (preddef_elim_clf P)
                                  | PPredDef r xs P Q => 
                                                  let Q':= preddef_elim_clf Q in  
                                                   prop_sub [(sprop r xs P)] Q'
                                                  | _ => p
                                          end
                                  end.
Proof. induction p; intros; reflexivity. Qed.
                                                         

Theorem preddef_elim_clf_atom_naive: forall P,
  legal P ->
  combined_layer_form P ->
  atom_naive (preddef_elim_clf P).
Proof.
  intros. induction H0; subst.
  + rewrite preddef_elim_clf_unfold_one_iteration.
      apply layer_form_layer_formb in H0 as H1. rewrite H1.
      now apply preddef_elim_lf_atom_naive.
  + simpl. destruct (atom_naiveb P) eqn : E.
      - apply atom_naive_atom_naiveb in E. 
         apply preddef_elim_lf_atom_naive. now inversion H. now repeat constructor.
      - inversion H; subst. constructor. tauto.
  + simpl. destruct (atom_naiveb P && atom_naiveb Q) eqn:E.
      - apply andb_true_iff in E. destruct E. rewrite <- atom_naive_atom_naiveb in *.
         apply preddef_elim_lf_atom_naive. easy. now repeat constructor. 
      - inversion H; subst. constructor; tauto.
  + simpl. destruct (atom_naiveb P && atom_naiveb Q) eqn:E.
      - apply andb_true_iff in E. destruct E. rewrite <- atom_naive_atom_naiveb in *.
         apply preddef_elim_lf_atom_naive. easy. now repeat constructor. 
      - inversion H; subst. constructor; tauto.
  + simpl. destruct (atom_naiveb P && atom_naiveb Q) eqn:E.
      - apply andb_true_iff in E. destruct E. rewrite <- atom_naive_atom_naiveb in *.
         apply preddef_elim_lf_atom_naive. easy. now repeat constructor. 
      - inversion H; subst. constructor; tauto.
  + simpl. destruct (atom_naiveb P && atom_naiveb Q) eqn:E.
      - apply andb_true_iff in E. destruct E. rewrite <- atom_naive_atom_naiveb in *.
         apply preddef_elim_lf_atom_naive. easy. now repeat constructor. 
      - inversion H; subst. constructor; tauto.
  + simpl. destruct (atom_naiveb P) eqn : E.
      - apply atom_naive_atom_naiveb in E. 
         apply preddef_elim_lf_atom_naive. now inversion H. now repeat constructor.
      - inversion H; subst. constructor. tauto.
  + simpl. destruct (atom_naiveb P) eqn : E.
      - apply atom_naive_atom_naiveb in E. 
         apply preddef_elim_lf_atom_naive. now inversion H. now repeat constructor.
      - inversion H; subst. constructor. tauto.
  + simpl. apply atom_naive_atom_naiveb in H0 as H2.
       rewrite H2. rewrite andb_true_l.
       destruct (layer_formb Q) eqn:E.
       - apply layer_form_layer_formb in E. apply preddef_elim_lf_atom_naive. easy. now constructor.
       - apply prop_sub_atom_naive. repeat constructor. easy. apply IHcombined_layer_form.
         inversion H; subst. apply reduce_arg_pred_legal with (r:=r) in H9. simpl in H9. cname. 
Qed.

Lemma preddef_elim_clf_keep_pred_legal: forall P args,
  pred_legal P args ->
  pred_legal (preddef_elim_clf P) args.
Proof.
  intros. induction H; simpl; try now constructor.
  + simpl. destruct (atom_naiveb P) eqn: E. 
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - now constructor. 
  + destruct (atom_naiveb P1 && atom_naiveb P2).
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - now constructor.
  + destruct (atom_naiveb P1 && atom_naiveb P2).
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - now constructor.
  + destruct (atom_naiveb P1 && atom_naiveb P2).
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - now constructor.
  + destruct (atom_naiveb P1 && atom_naiveb P2).
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - now constructor.
  + simpl. destruct (atom_naiveb P) eqn: E. 
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - now constructor. 
  + simpl. destruct (atom_naiveb P) eqn: E. 
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - now constructor. 
  + simpl. destruct (atom_naiveb P && layer_formb Q).
      - apply preddef_elim_lf_keep_pred_legal. now constructor.
      - apply preddef_unfold_keep_pred_legal. now constructor.
Qed.

Corollary preddef_elim_clf_keep_legal: forall P,
  legal P -> legal (preddef_elim_clf P).
Proof. intros. now apply preddef_elim_clf_keep_pred_legal. Qed.


Lemma preddef_elim_clf_keep_no_pred_free_occur: forall r P,
  pred_free_occur r P = 0 ->
  pred_free_occur r (preddef_elim_clf P) = 0.
Proof.
  induction P; intros; try easy.
  + simpl. destruct (atom_naiveb P) eqn: E. 
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - simpl. tauto.
  + simpl. destruct (atom_naiveb P1 && atom_naiveb P2).
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy. 
  + simpl. destruct (atom_naiveb P1 && atom_naiveb P2).
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy. 
  + simpl. destruct (atom_naiveb P1 && atom_naiveb P2).
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy. 
  + simpl. destruct (atom_naiveb P1 && atom_naiveb P2).
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy.
  + simpl. destruct (atom_naiveb P) eqn: E. 
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - simpl. tauto.    
  + simpl. destruct (atom_naiveb P) eqn: E. 
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - simpl. tauto.
  + simpl. destruct (atom_naiveb P1 && layer_formb P2).
      - now apply preddef_elim_lf_keep_no_pred_free_occur.
      - apply preddef_unfold_keep_no_pred_free_occur.
         zero_r H. simpl. cname.
Qed.

Theorem preddef_elim_clf_naive: forall P,
  closed P ->
  legal P ->
  combined_layer_form P ->
  naive (preddef_elim_clf P).
Proof.
  intros. induction H1.
  + rewrite preddef_elim_clf_unfold_one_iteration. apply layer_form_layer_formb in H1 as H2.
      rewrite H2. now apply preddef_elim_lf_naive.
  + rewrite preddef_elim_clf_unfold_one_iteration. destruct (layer_formb [[¬ P]]) eqn:E.
      - rewrite <- layer_form_layer_formb in E. now apply preddef_elim_lf_naive.
      - constructor. rewrite  PNot_keep_closed in H. inversion H0; subst. tauto.
  + rewrite preddef_elim_clf_unfold_one_iteration. destruct (layer_formb [[P /\ Q]]) eqn:E.
      - rewrite <- layer_form_layer_formb in E. now apply preddef_elim_lf_naive.
      - apply PAnd_keep_closed in H. destruct H.  inversion H0; subst. constructor; tauto.
  + rewrite preddef_elim_clf_unfold_one_iteration. destruct (layer_formb [[P \/ Q]]) eqn:E.
      - rewrite <- layer_form_layer_formb in E. now apply preddef_elim_lf_naive.
      - apply POr_keep_closed in H. destruct H.  inversion H0; subst. constructor; tauto.
  + rewrite preddef_elim_clf_unfold_one_iteration. destruct (layer_formb [[P -> Q]]) eqn:E.
      - rewrite <- layer_form_layer_formb in E. now apply preddef_elim_lf_naive.
      - apply PImpl_keep_closed in H. destruct H.  inversion H0; subst. constructor; tauto.
  + rewrite preddef_elim_clf_unfold_one_iteration. destruct (layer_formb [[P <-> Q]]) eqn:E.
      - rewrite <- layer_form_layer_formb in E. now apply preddef_elim_lf_naive.
      - apply PIff_keep_closed in H. destruct H.  inversion H0; subst. constructor; tauto.
  + rewrite preddef_elim_clf_unfold_one_iteration. destruct (layer_formb [[∀x, P]]) eqn:E.
      - rewrite <- layer_form_layer_formb in E. now apply preddef_elim_lf_naive.
      - apply PForall_keep_closed in H. inversion H0; subst. constructor; tauto.
  + rewrite preddef_elim_clf_unfold_one_iteration. destruct (layer_formb [[∃x, P]]) eqn:E.
      - rewrite <- layer_form_layer_formb in E. now apply preddef_elim_lf_naive.
      - apply PExists_keep_closed in H. inversion H0; subst. constructor; tauto.
  + simpl. apply atom_naive_atom_naiveb in H1 as H3. rewrite H3. rewrite andb_true_l.
       destruct ( layer_formb Q) eqn : E.
       - apply preddef_elim_lf_naive. easy. easy.
         rewrite <- layer_form_layer_formb in E. now constructor.
       - apply preddef_unfold_naive.
         * inversion H0; subst. constructor. easy. now apply preddef_elim_clf_keep_pred_legal.
         * hnf in *. intros. simpl in *. specialize H with r0. cname.
            zero_r H.  now apply preddef_elim_clf_keep_no_pred_free_occur.
         * apply PPredDef_closed in H. now apply closed_atom_naive_is_naive. 
         * inversion H0; subst. apply reduce_arg_pred_legal with (r:=r) in H10.
            simpl in H10. cname. now apply preddef_elim_clf_atom_naive.
Qed.

Theorem preddef_elim_clf_bstar: forall P,
  legal P ->
  LAM.bstar (prop2tm P) (prop2tm (preddef_elim_clf P)).
Proof.
  induction P; intros; test_bstar; simpl preddef_elim_clf.
  + destruct (atom_naiveb P).
      - inversion H; subst. now apply preddef_elim_lf_bstar.
      - simpl. inversion H; subst. test_bstar.
 + destruct (atom_naiveb P1 && atom_naiveb P2).
      - inversion H; subst. now apply preddef_elim_lf_bstar.
      - simpl. inversion H; subst. test_bstar.
 + destruct (atom_naiveb P1 && atom_naiveb P2).
      - inversion H; subst. now apply preddef_elim_lf_bstar.
      - simpl. inversion H; subst. test_bstar.
 + destruct (atom_naiveb P1 && atom_naiveb P2).
      - inversion H; subst. now apply preddef_elim_lf_bstar.
      - simpl. inversion H; subst. test_bstar.
 + destruct (atom_naiveb P1 && atom_naiveb P2).
      - inversion H; subst. now apply preddef_elim_lf_bstar.
      - simpl. inversion H; subst. test_bstar.
 + destruct (atom_naiveb P).
      - inversion H; subst. now apply preddef_elim_lf_bstar.
      - simpl. inversion H; subst. test_bstar.
 + destruct (atom_naiveb P).
      - inversion H; subst. now apply preddef_elim_lf_bstar.
      - simpl. inversion H; subst. test_bstar.
 + destruct (atom_naiveb P1 && layer_formb P2).
      - now apply preddef_elim_lf_bstar.
      - inversion H; subst. apply reduce_arg_pred_legal with (r:=r) in H6.
        simpl in H6. cname. etransitivity. 2: apply preddef_unfold_bstar.
        * simpl. test_bstar.  
        * inversion H; subst. constructor. easy. now apply preddef_elim_clf_keep_pred_legal.
Qed.  

Lemma atom_naive_preddef_elim_clf: forall P,
  atom_naive P -> preddef_elim_clf P = P.
Proof.
  intros. rewrite preddef_elim_clf_unfold_one_iteration.
  assert (layer_formb P = true). 
  apply layer_form_layer_formb. now constructor.
  rewrite H0. induction H; easy. 
Qed.

Local Ltac preddef_elim_lf_proof P Q:=
  simpl; destruct (atom_naiveb P && atom_naiveb Q) eqn: E; try easy;
  apply andb_true_iff in E; rewrite <- 2 atom_naive_atom_naiveb in E; destruct E;
      repeat rewrite atom_naive_preddef_elim_clf; now try constructor.

Lemma PAnd_preddef_elim_clf: forall P Q,
  preddef_elim_clf (PAnd P Q)  = PAnd (preddef_elim_clf P) (preddef_elim_clf Q).
Proof. intros. preddef_elim_lf_proof P Q. Qed.

Lemma POr_preddef_elim_clf: forall P Q,
  preddef_elim_clf (POr P Q)  = POr (preddef_elim_clf P) (preddef_elim_clf Q).
Proof. intros. preddef_elim_lf_proof P Q. Qed.

Lemma PImpl_preddef_elim_clf: forall P Q,
  preddef_elim_clf (PImpl P Q)  = PImpl (preddef_elim_clf P) (preddef_elim_clf Q).
Proof. intros. preddef_elim_lf_proof P Q. Qed.

Lemma PIff_preddef_elim_clf: forall P Q,
  preddef_elim_clf (PIff P Q)  = PIff (preddef_elim_clf P) (preddef_elim_clf Q).
Proof. intros. preddef_elim_lf_proof P Q. Qed.

Lemma PNot_preddef_elim_clf: forall P,
  preddef_elim_clf (PNot P)  = PNot (preddef_elim_clf P).
Proof. 
  intros. simpl. destruct (atom_naiveb P) eqn:E; try easy.
  apply atom_naive_atom_naiveb in E.  now rewrite atom_naive_preddef_elim_clf.
Qed.

Lemma PForall_preddef_elim_clf: forall x P,
  preddef_elim_clf (PForall x P)  = PForall x (preddef_elim_clf P).
Proof. 
  intros. simpl. destruct (atom_naiveb P) eqn:E; try easy.
  apply atom_naive_atom_naiveb in E.  now rewrite atom_naive_preddef_elim_clf.
Qed.

Lemma PExists_preddef_elim_clf: forall x P,
  preddef_elim_clf (PExists x P)  = PExists x (preddef_elim_clf P).
Proof. 
  intros. simpl. destruct (atom_naiveb P) eqn:E; try easy.
  apply atom_naive_atom_naiveb in E.  now rewrite atom_naive_preddef_elim_clf.
Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*      Eliminate all predicates in propositions    *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Fixpoint preddef_elim (p:prop): prop:=
  match simpl_preddef_formb p with
  | true => preddef_elim_clf p
  | false => 
        match p with
         | PNot P => PNot (preddef_elim P)
         | PAnd P1 P2 => PAnd (preddef_elim P1) (preddef_elim P2)
         | POr P1 P2 => POr (preddef_elim P1) (preddef_elim P2)
         | PImpl P1 P2 => PImpl (preddef_elim P1) (preddef_elim P2)
         | PIff P1 P2 => PIff (preddef_elim P1) (preddef_elim P2)
         | PForall x P => PForall x (preddef_elim P)
         | PExists x P => PExists x (preddef_elim P)
         | PPredDef r xs P Q => 
                let P':= preddef_elim P in
                let Q':= preddef_elim Q in  
                    prop_sub [(sprop r xs P')] Q'
         | _ => p
         end
  end.

Lemma preddef_elim_unfold_one_iteration: forall p,
  preddef_elim p = 
  match simpl_preddef_formb p with
  | true => preddef_elim_clf p
  | false => 
        match p with
         | PNot P => PNot (preddef_elim P)
         | PAnd P1 P2 => PAnd (preddef_elim P1) (preddef_elim P2)
         | POr P1 P2 => POr (preddef_elim P1) (preddef_elim P2)
         | PImpl P1 P2 => PImpl (preddef_elim P1) (preddef_elim P2)
         | PIff P1 P2 => PIff (preddef_elim P1) (preddef_elim P2)
         | PForall x P => PForall x (preddef_elim P)
         | PExists x P => PExists x (preddef_elim P)
         | PPredDef r xs P Q => 
                let P':= preddef_elim P in
                let Q':= preddef_elim Q in  
                    prop_sub [(sprop r xs P')] Q'
         | _ => p
         end
  end.
Proof. intros. destruct p; reflexivity. Qed.

Theorem preddef_elim_atom_naive: forall P,
  legal P ->
  atom_naive (preddef_elim P).
Proof.
  intros. induction P; simpl; try constructor.
  + destruct (simpl_preddef_formb P) eqn : E.
      -  pose proof preddef_elim_clf_atom_naive (PNot P).
         apply combined_layer_form_simpl_preddef_formb in E. apply H0; try easy. now constructor.
      - inversion H; subst. constructor; tauto. 
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn:E.
      - apply andb_true_iff in E. destruct E. 
         apply combined_layer_form_simpl_preddef_formb in H0.
         apply combined_layer_form_simpl_preddef_formb in H1.
        pose proof preddef_elim_clf_atom_naive (PAnd P1 P2). apply H2; try easy. now constructor.
      - inversion H; subst. constructor; tauto.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn:E.
      - apply andb_true_iff in E. destruct E. 
         apply combined_layer_form_simpl_preddef_formb in H0.
         apply combined_layer_form_simpl_preddef_formb in H1.
        pose proof preddef_elim_clf_atom_naive (POr P1 P2). apply H2; try easy. now constructor.
      - inversion H; subst. constructor; tauto.
   + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn:E.
      - apply andb_true_iff in E. destruct E. 
         apply combined_layer_form_simpl_preddef_formb in H0.
         apply combined_layer_form_simpl_preddef_formb in H1.
        pose proof preddef_elim_clf_atom_naive (PImpl P1 P2). apply H2; try easy. now constructor.
      - inversion H; subst. constructor; tauto.
    + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn:E.
      - apply andb_true_iff in E. destruct E. 
         apply combined_layer_form_simpl_preddef_formb in H0.
         apply combined_layer_form_simpl_preddef_formb in H1.
        pose proof preddef_elim_clf_atom_naive (PIff P1 P2). apply H2; try easy. now constructor.
      - inversion H; subst. constructor; tauto.
  + destruct (simpl_preddef_formb P) eqn : E.
      -  pose proof preddef_elim_clf_atom_naive (PForall x P).
         apply combined_layer_form_simpl_preddef_formb in E. apply H0; try easy. now constructor.
      - inversion H; subst. constructor; tauto. 
  + destruct (simpl_preddef_formb P) eqn : E.
      -  pose proof preddef_elim_clf_atom_naive (PExists x P).
         apply combined_layer_form_simpl_preddef_formb in E. apply H0; try easy. now constructor.
      - inversion H; subst. constructor; tauto. 
  + destruct (atom_naiveb P1 && simpl_preddef_formb P2) eqn : E.
      - apply andb_true_iff in E. destruct E. apply atom_naive_atom_naiveb in H0.
        apply combined_layer_form_simpl_preddef_formb in H1.
        pose proof preddef_elim_clf_atom_naive (PPredDef r xs P1 P2).
        apply H2. easy. now constructor.
      - inversion H; subst.  apply prop_sub_atom_naive. repeat constructor. tauto.
        apply reduce_arg_pred_legal with (r:=r) in H6. simpl in H6. cname. 
Qed.

Lemma preddef_elim_keep_pred_legal: forall P args,
  pred_legal P args ->
  pred_legal (preddef_elim P) args.
Proof.
  intros. induction H; simpl; try now constructor.
  + destruct (simpl_preddef_formb P) eqn : E.
      - apply preddef_elim_clf_keep_pred_legal with (P:= PNot P). now constructor.
      - now constructor. 
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - apply preddef_elim_clf_keep_pred_legal with (P:= PAnd P1 P2). now constructor.
      - now constructor.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - apply preddef_elim_clf_keep_pred_legal with (P:= POr P1 P2). now constructor.
      - now constructor.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - apply preddef_elim_clf_keep_pred_legal with (P:= PImpl P1 P2). now constructor.
      - now constructor.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - apply preddef_elim_clf_keep_pred_legal with (P:= PIff P1 P2). now constructor.
      - now constructor.
  + destruct (simpl_preddef_formb P) eqn : E.
      - apply preddef_elim_clf_keep_pred_legal with (P:= PForall x P). now constructor.
      - now constructor. 
  + destruct (simpl_preddef_formb P) eqn : E.
      - apply preddef_elim_clf_keep_pred_legal with (P:= PExists x P). now constructor.
      - now constructor. 
  + destruct (atom_naiveb P && simpl_preddef_formb Q).
      - apply preddef_elim_clf_keep_pred_legal with (P:=PPredDef r xs P Q). now constructor.
      - apply preddef_unfold_keep_pred_legal. now constructor.
Qed.

Corollary preddef_elim_keep_legal: forall P,
  legal P -> legal (preddef_elim P).
Proof. intros. now apply preddef_elim_keep_pred_legal. Qed.

Lemma preddef_elim_keep_no_pred_free_occur: forall r P,
  pred_free_occur r P = 0 ->
  pred_free_occur r (preddef_elim P) = 0.
Proof.
  induction P; intros; try easy.
  + simpl. destruct (simpl_preddef_formb P) eqn: E; try tauto. 
      now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=PNot P).
  + simpl. destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=PAnd P1 P2).
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy. 
  + simpl. destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=POr P1 P2).
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy. 
  + simpl. destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=PImpl P1 P2).
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy. 
  + simpl. destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=PIff P1 P2).
      - simpl. zero_r H. rewrite IHP1. now rewrite IHP2. easy. 
  + simpl. destruct (simpl_preddef_formb P) eqn: E; try tauto. 
      now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=PForall x P).  
  + simpl. destruct (simpl_preddef_formb P) eqn: E; try tauto. 
      now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=PExists x P).  
  + simpl. destruct (atom_naiveb P1 && simpl_preddef_formb P2).
      - now apply preddef_elim_clf_keep_no_pred_free_occur with (P:=PPredDef r0 xs P1 P2). 
      - apply preddef_unfold_keep_no_pred_free_occur.
         zero_r H. simpl. cname.
         * now rewrite IHP1.
         * rewrite IHP1; try easy. now rewrite IHP2. 
Qed.

Corollary preddef_elim_keep_closed: forall P,
  closed P -> closed (preddef_elim P).
Proof. intros. hnf in *. intros. specialize H with r. now apply preddef_elim_keep_no_pred_free_occur. Qed. 

Definition good(P:prop):= 
  closed P /\ legal P.
  
Definition goodb (P:prop):=
  legalb P && closedb P.
  
Corollary good_goodb: forall P,
  good P <->  goodb P = true.
Proof.
  unfold good. unfold goodb. split; intros. 
  + destruct H as [? ? ].
      apply closed_closedb in H.
      apply legal_legalb in H0.
      rewrite H. now rewrite H0. 
  + apply andb_prop in H. destruct H. 
      split.  
      - now apply closed_closedb.
      - now apply legal_legalb.
Qed.     

Lemma naive_is_good: forall P, 
  naive P -> good P.
Proof.
  intros. unfold good. split. 
  + unfold closed. intros. now apply naive_no_pred.
  + now apply naive_legal.
Qed.

Theorem preddef_elim_naive: forall P,
  good P ->
  naive (preddef_elim P).
Proof.
  intros. unfold good in H. destruct H. induction P; simpl; try constructor.
  + hnf in H. specialize H with (atom_pred a). simpl in H. rewrite atom_pred_pred_atom_occur in H. discriminate.
  + destruct (simpl_preddef_formb P) eqn: E.
      - rewrite <- combined_layer_form_simpl_preddef_formb in E. 
         apply preddef_elim_clf_naive with (P:=PNot P); try easy. now constructor.
      - constructor. rewrite PNot_keep_closed in H. inversion H0; subst. tauto.  
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn: E.
      - apply andb_true_iff in E. destruct E. 
        apply combined_layer_form_simpl_preddef_formb in H1.
        apply combined_layer_form_simpl_preddef_formb in H2.
         apply preddef_elim_clf_naive with (P:=PAnd P1 P2); try easy. now constructor.
      - inversion H0; subst. rewrite PAnd_keep_closed in H. constructor; tauto.  
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn: E.
      - apply andb_true_iff in E. destruct E. 
        apply combined_layer_form_simpl_preddef_formb in H1.
        apply combined_layer_form_simpl_preddef_formb in H2.
         apply preddef_elim_clf_naive with (P:=POr P1 P2); try easy. now constructor.
      - inversion H0; subst. rewrite POr_keep_closed in H. constructor; tauto. 
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn: E.
      - apply andb_true_iff in E. destruct E. 
        apply combined_layer_form_simpl_preddef_formb in H1.
        apply combined_layer_form_simpl_preddef_formb in H2.
         apply preddef_elim_clf_naive with (P:=PImpl P1 P2); try easy. now constructor.
      - inversion H0; subst. rewrite PImpl_keep_closed in H. constructor; tauto.  
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2) eqn: E.
      - apply andb_true_iff in E. destruct E. 
        apply combined_layer_form_simpl_preddef_formb in H1.
        apply combined_layer_form_simpl_preddef_formb in H2.
         apply preddef_elim_clf_naive with (P:=PIff P1 P2); try easy. now constructor.
      - inversion H0; subst. rewrite PIff_keep_closed in H. constructor; tauto.  
  + destruct (simpl_preddef_formb P) eqn: E.
      - rewrite <- combined_layer_form_simpl_preddef_formb in E. 
         apply preddef_elim_clf_naive with (P:=PForall x P); try easy. now constructor.
      - constructor. rewrite PForall_keep_closed in H. inversion H0; subst. tauto.  
  + destruct (simpl_preddef_formb P) eqn: E.
      - rewrite <- combined_layer_form_simpl_preddef_formb in E. 
         apply preddef_elim_clf_naive with (P:=PExists x P); try easy. now constructor.
      - constructor. rewrite PExists_keep_closed in H. inversion H0; subst. tauto.  
  + destruct (atom_naiveb P1 && simpl_preddef_formb P2) eqn : E.
       - apply andb_true_iff in E. destruct E. 
          apply atom_naive_atom_naiveb in H1.
          apply combined_layer_form_simpl_preddef_formb in H2.
          apply preddef_elim_clf_naive with (P:=PPredDef r xs P1 P2); try easy. now constructor.
       - apply preddef_unfold_naive.
         * inversion H0; subst. constructor. now apply preddef_elim_keep_pred_legal.
            now apply preddef_elim_keep_pred_legal.
         * hnf in *. intros. simpl in *. specialize H with r0. cname.
            zero_r H. f_equal. now apply preddef_elim_keep_no_pred_free_occur.  
            zero_r H.  apply preddef_elim_keep_no_pred_free_occur in H. rewrite H.
            now apply preddef_elim_keep_no_pred_free_occur. 
         * apply PPredDef_closed in H. inversion H0; subst. tauto. 
         * inversion H0; subst. apply reduce_arg_pred_legal with (r:=r) in H7.
            simpl in H7. cname. now apply preddef_elim_atom_naive.
Qed.

Theorem preddef_elim_bstar: forall P,
  legal P ->
  LAM.bstar (prop2tm P) (prop2tm (preddef_elim P)).
Proof.
  induction P; intros; test_bstar; simpl preddef_elim.
  + destruct (simpl_preddef_formb P).
      - inversion H; subst. now apply preddef_elim_clf_bstar.
      - simpl. inversion H; subst. test_bstar.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - inversion H; subst. now apply preddef_elim_clf_bstar.
      - simpl. inversion H; subst. test_bstar.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - inversion H; subst. now apply preddef_elim_clf_bstar.
      - simpl. inversion H; subst. test_bstar.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - inversion H; subst. now apply preddef_elim_clf_bstar.
      - simpl. inversion H; subst. test_bstar.
  + destruct (simpl_preddef_formb P1 && simpl_preddef_formb P2).
      - inversion H; subst. now apply preddef_elim_clf_bstar.
      - simpl. inversion H; subst. test_bstar.
  + destruct (simpl_preddef_formb P).
      - inversion H; subst. now apply preddef_elim_clf_bstar.
      - simpl. inversion H; subst. test_bstar.
  + destruct (simpl_preddef_formb P).
      - inversion H; subst. now apply preddef_elim_clf_bstar.
      - simpl. inversion H; subst. test_bstar.
  + destruct (atom_naiveb P1 && simpl_preddef_formb P2).
      - now apply preddef_elim_clf_bstar.
      - inversion H; subst. apply reduce_arg_pred_legal with (r:=r) in H6.
        simpl in H6. cname. etransitivity. 2: apply preddef_unfold_bstar.
        * simpl. test_bstar. apply tm_add_binders_bstar. tauto.
        * inversion H; subst. constructor. now apply preddef_elim_keep_pred_legal. 
           now apply preddef_elim_keep_pred_legal.
Qed.  

Local Ltac simple_check_good:=
  repeat match goal with
  | H: context [prop_sub [(svar _ _)] _ ] |- _=>  rewrite <- prop_var_sub_prop_sub in H
  | H: good _ |- _ => unfold good in H
  | |- good _ => unfold good; split
  | |- naive (preddef_elim _) => apply preddef_elim_naive
  | |- closed (prop_sub [(sprop _ _ _)] _) => apply preddef_unfold_keep_closed
  | |- legal (prop_sub [(sprop _ _ _)] _) => apply preddef_unfold_keep_legal
  | |- Forall only_var_sub _ => now repeat constructor
  | |- context [prop_sub [(svar _ _)] _ ] =>  rewrite <- prop_var_sub_prop_sub
  | |- naive (prop_var_sub _ _) => apply prop_var_sub_keep_naive_iff
  | |- legal (prop_var_sub _ _) => apply prop_var_sub_keep_pred_legal
  | |- closed (prop_var_sub _ _) => apply prop_var_sub_keep_closed
  end; try tauto.

Ltac apply_CR:=
  let H := fresh "H" in
  let H0:= fresh "H" in
  match goal with
  | |- aeq ?P ?Q => assert (naive P) as H by simple_check_good; assert (naive Q) as H0 by simple_check_good; 
                             apply aeq_FOL_LAM; apply naive_prop2tm_bnf in H; apply naive_prop2tm_bnf in H0
  end.

Corollary preddef_elim_keep_good: forall P,
  good P ->
  good (preddef_elim P).
Proof.
  intros. simple_check_good.
  + now apply preddef_elim_keep_closed.
  + now apply preddef_elim_keep_legal.
Qed. 

Corollary legal_preddef_elim_keep_no_free_occur: forall x P,
  legal P ->
  free_occur x P = 0 ->
  free_occur x (preddef_elim P) = 0.
Proof.
  intros. FOL2LAM. eapply LAM.bstar_keep_no_free_occur. 2: apply H0.
  now apply preddef_elim_bstar.
Qed.

Corollary subst_var_preddef_elim_aeq: forall P x t,
  good P ->
  aeq (prop_sub [(svar x t)] (preddef_elim P)) (preddef_elim (prop_sub [(svar x t)] P)).
Proof.
  intros. simple_check_good. apply_CR.
  apply LAM.two_bnf_aeq  with (M:= LAM.app (LAM.abs (uvar x) (prop2tm P)) (term2tm t)); try easy.
  + constructor 3 with (LAM.app (LAM.abs x (prop2tm (preddef_elim P)))(term2tm t)).
    - test_bstar. apply preddef_elim_bstar; simple_check_good.
    - repeat constructor. eapply beta_congruence_r. 2: constructor.  symmetry.
       apply prop_var_sub_FOL_LAM. simple_check_good. 
  + econstructor 3. repeat constructor. eapply bstar_congruence_l.
    pose proof prop_var_sub_FOL_LAM P [(svar x t)].  apply H2. simple_check_good. 
    apply preddef_elim_bstar; simple_check_good.
Qed.

Corollary preddef_unfold_preddef_elim_aeq: forall r xs P Q,
  good [[let r xs:= P in Q]] ->
  aeq (preddef_elim [[let r xs:= P in Q]]) (preddef_elim (prop_sub [(sprop r xs P)] Q)).
Proof.
  intros. apply_CR.
  apply LAM.two_bnf_aeq with (M:= prop2tm [[let r xs:= P in Q]]); try easy.
  + apply preddef_elim_bstar. simple_check_good.
  + constructor 3 with (prop2tm (prop_sub [(sprop r xs P)] Q)).
      - apply preddef_unfold_bstar; simple_check_good.
      - apply preddef_elim_bstar; simple_check_good.
Qed. 

Lemma preddef_elim_aeq: forall P Q,
  aeq P Q ->
  good P ->
  good Q ->
  aeq (preddef_elim P) (preddef_elim Q).
Proof.
  intros. assert (naive (preddef_elim P)) by simple_check_good.
  assert (naive (preddef_elim Q)) by simple_check_good.
  FOL2LAM.
  pose proof LAM.bstar_preserve_aeq (prop2tm P) (prop2tm (preddef_elim P)) (prop2tm Q).
  apply H4 in H. clear H4. 2: apply preddef_elim_bstar; now unfold good in H0.
  destruct H as [M ?].  transitivity M. now symmetry.
  apply naive_prop2tm_bnf in H2.
  apply naive_prop2tm_bnf in H3.
  destruct H. symmetry in H4. apply LAM.aeq_bnf_then_bnf in H4. 2: easy.
  apply LAM.two_bnf_aeq with (M:= prop2tm Q); try easy.
  apply preddef_elim_bstar; now unfold good in H1.
Qed. 

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*** Properties of alpha equivalence  ***)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Corollary aeq_refl: Reflexive aeq.
Proof. unfold Reflexive. intros. FOL2LAM. LAM.aeq_solve. Qed.

Corollary aeq_sym: Symmetric aeq.
Proof. unfold Symmetric. intros. FOL2LAM. LAM.aeq_solve. Qed.

Corollary aeq_trans: Transitive aeq.
Proof. unfold Transitive. intros. FOL2LAM. LAM.aeq_solve. Qed. 

Add Relation prop aeq reflexivity proved by aeq_refl symmetry proved by aeq_sym 
        transitivity proved by aeq_trans as aeq_equivalence.

Corollary aeq_PAnd: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PAnd P1 Q1) (PAnd P2 Q2).
Proof. intros. FOL2LAM. simpl. LAM.aeq_solve. Qed. 

Corollary aeq_POr: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (POr P1 Q1) (POr P2 Q2).
Proof. intros. FOL2LAM. simpl. LAM.aeq_solve. Qed. 

Corollary aeq_PImpl: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PImpl P1 Q1) (PImpl P2 Q2).
Proof. intros. FOL2LAM. simpl. LAM.aeq_solve. Qed.

Corollary aeq_PIff: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PIff P1 Q1) (PIff P2 Q2).
Proof. intros. FOL2LAM. simpl. LAM.aeq_solve. Qed.  

Corollary aeq_PNot: forall P1 P2 Q1 Q2,
  aeq P1 P2 ->
  aeq Q1 Q2 ->
  aeq (PAnd P1 Q1) (PAnd P2 Q2).
Proof. intros. FOL2LAM. simpl. LAM.aeq_solve. Qed.

Corollary aeq_PForall: forall x P1 P2,
  aeq P1 P2 ->
  aeq (PForall x P1) (PForall x P2).
Proof. intros. FOL2LAM. simpl. LAM.aeq_solve. Qed.

Corollary aeq_PExists: forall x P1 P2,
  aeq P1 P2 ->
  aeq (PExists x P1) (PExists x P2).
Proof. intros. FOL2LAM. simpl. LAM.aeq_solve. Qed.

Ltac saeq:=
  repeat match goal with
   | H: context[alpha_eq nil ?t1 ?t2] |- _  => let ph:=fresh "H" in 
                                                  assert (alpha_eq nil t1 t2 = aeq t1 t2) as ph;
                                                  [reflexivity| rewrite ph in H; clear ph]
   | |- alpha_eq nil ?t1 ?t2 => let ph:=fresh "H" in 
                                  assert (alpha_eq nil t1 t2 = aeq t1 t2) as ph;
                                  [reflexivity| rewrite ph;clear ph]
   | H: aeq ?t1 ?t2 |- aeq ?t1 ?t2 => exact H
   | |- aeq ?t ?t => apply reflexivity
   | H: aeq ?t1 ?t2 |- aeq ?t2 ?t1 => symmetry
(*    | [H:aeq (abs ?s ?t1)(abs ?s ?t2) |- aeq ?t1 ?t2] => apply remove_bind_aeq in H;tauto *)
(*    | [|- aeq (subst ?st _) (subst ?st _)] => apply subst_same_st_aeq *)
   | H: aeq ?t1 ?t2 |- aeq ?t1 ?t3 => transitivity t2;[| clear H]
   | H: aeq ?t1 ?t2 |- aeq ?t3 ?t1 => transitivity t2;[clear H|]
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
   | |- aeq (prop_sub ((svar ?x ?t)::nil) (preddef_elim ?p))
               (preddef_elim (prop_sub ((svar ?x ?t)::nil) ?p)) => apply subst_var_preddef_elim_aeq
   | |- aeq (preddef_elim (prop_sub ((svar ?x ?t)::nil)  ?p)) 
                (prop_sub ((svar ?x ?t)::nil)  (preddef_elim ?p))=> symmetry; apply subst_var_preddef_elim_aeq
   | |- _ => try tauto
  end.

Lemma atom_naive_preddef_elim: forall P,
  atom_naive P -> preddef_elim P = P.
Proof.
  intros. rewrite preddef_elim_unfold_one_iteration.
  assert (simpl_preddef_formb P = true).
  apply combined_layer_form_simpl_preddef_formb. 
  now repeat constructor.
  rewrite H0. now apply atom_naive_preddef_elim_clf .
Qed.

Local Ltac preddef_elim_proof P Q:=
  simpl; destruct (simpl_preddef_formb P && simpl_preddef_formb Q) eqn: E; try easy;
  rewrite 2 preddef_elim_unfold_one_iteration;
  apply andb_true_iff in E; destruct E as [H H0]; rewrite H; rewrite H0;
  destruct (atom_naiveb P && atom_naiveb Q) eqn: E; try easy;
  apply andb_true_iff in E; rewrite <- 2 atom_naive_atom_naiveb in E; destruct E;
  repeat rewrite atom_naive_preddef_elim_clf; try easy; now try constructor.

Lemma PAnd_preddef_elim: forall P Q,
  preddef_elim (PAnd P Q)  = PAnd (preddef_elim P) (preddef_elim Q).
Proof. intros. preddef_elim_proof P Q.  Qed.

Lemma POr_preddef_elim: forall P Q,
  preddef_elim (POr P Q)  = POr (preddef_elim P) (preddef_elim Q).
Proof. intros. preddef_elim_proof P Q. Qed.

Lemma PImpl_preddef_elim: forall P Q,
  preddef_elim (PImpl P Q)  = PImpl (preddef_elim P) (preddef_elim Q).
Proof. intros. preddef_elim_proof P Q. Qed.

Lemma PIff_preddef_elim: forall P Q,
  preddef_elim (PIff P Q)  = PIff (preddef_elim P) (preddef_elim Q).
Proof. intros. preddef_elim_proof P Q. Qed.

Lemma PNot_preddef_elim: forall P,
  preddef_elim (PNot P)  = PNot (preddef_elim P).
Proof. 
  intros. simpl. rewrite preddef_elim_unfold_one_iteration.
  destruct (simpl_preddef_formb P) eqn:E; try easy.
  destruct (atom_naiveb P) eqn:E1 ; try easy.
  apply atom_naive_atom_naiveb in E1.  now rewrite atom_naive_preddef_elim_clf.
Qed.

Lemma PForall_preddef_elim: forall x P,
  preddef_elim (PForall x P)  = PForall x (preddef_elim P).
Proof. 
  intros. simpl. rewrite preddef_elim_unfold_one_iteration.
  destruct (simpl_preddef_formb P) eqn:E; try easy.
  destruct (atom_naiveb P) eqn:E1 ; try easy.
  apply atom_naive_atom_naiveb in E1.  now rewrite atom_naive_preddef_elim_clf.
Qed.

Lemma PExists_preddef_elim: forall x P,
  preddef_elim (PExists x P)  = PExists x (preddef_elim P).
Proof. 
   intros. simpl. rewrite preddef_elim_unfold_one_iteration.
  destruct (simpl_preddef_formb P) eqn:E; try easy.
  destruct (atom_naiveb P) eqn:E1 ; try easy.
  apply atom_naive_atom_naiveb in E1.  now rewrite atom_naive_preddef_elim_clf.
Qed.

Ltac simpl_preddef_elim:=
  repeat match goal with
  | |- context [preddef_elim (PAnd _ _ ) ] => rewrite PAnd_preddef_elim
  | |- context [preddef_elim (POr _ _ ) ] => rewrite POr_preddef_elim
  | |- context [preddef_elim (PImpl _ _ ) ] => rewrite PImpl_preddef_elim
  | |- context [preddef_elim (PIff _ _ ) ] => rewrite PIff_preddef_elim
  | |- context [preddef_elim (PNot _ ) ] => rewrite PNot_preddef_elim
  | |- context [preddef_elim (PForall _ _ ) ] => rewrite PForall_preddef_elim
  | |- context [preddef_elim (PExists _ _ ) ] => rewrite PExists_preddef_elim
  | |- context [preddef_elim (PEq _ _)] => rewrite atom_naive_preddef_elim;[|constructor]
  | |- context [preddef_elim (PRel _ _)] => rewrite atom_naive_preddef_elim;[|constructor]
  | |- context [preddef_elim PTrue] => rewrite atom_naive_preddef_elim;[|constructor]
  | |- context [preddef_elim PFalse] => rewrite atom_naive_preddef_elim;[|constructor]
 end.
 
 Ltac simpl_preddef_elim_in H:=
  repeat match type of H with
  | context [preddef_elim (PAnd _ _ ) ]  => rewrite PAnd_preddef_elim in H
  | context [preddef_elim (POr _ _ ) ] => rewrite POr_preddef_elim in H
  | context [preddef_elim (PImpl _ _ ) ] => rewrite PImpl_preddef_elim in H
  | context [preddef_elim (PIff _ _ ) ] => rewrite PIff_preddef_elim in H
  | context [preddef_elim (PNot _ ) ] => rewrite PNot_preddef_elim in H
  | context [preddef_elim (PForall _ _ ) ] => rewrite PForall_preddef_elim in H
  | context [preddef_elim (PExists _ _ ) ] => rewrite PExists_preddef_elim in H
  | context [preddef_elim (PEq _ _)]  => rewrite atom_naive_preddef_elim in H;[|constructor]
  | context [preddef_elim (PRel _ _)]  => rewrite atom_naive_preddef_elim in H;[|constructor]
  | context [preddef_elim PTrue]   => rewrite atom_naive_preddef_elim in H;[|constructor]
  | context [preddef_elim PFalse] => rewrite atom_naive_preddef_elim in H;[|constructor]
 end.

Ltac cgood:= 
   repeat (try tauto; match goal with
   | |- Forall only_var_sub _ => repeat constructor
   | |- naive (preddef_elim _) => apply preddef_elim_naive
   | |- good (preddef_elim _) => apply preddef_elim_keep_good
   | |- legal (preddef_elim _) => apply preddef_elim_keep_legal
   | |- pred_legal (preddef_elim _) _ => apply preddef_elim_keep_pred_legal
   | |- closed (preddef_elim _) => apply preddef_elim_keep_closed
   | H: legal _ |- _ => unfold legal in H
   | |- legal _ => unfold legal
   | H: context [prop_sub [(svar _ _)] _ ] |- _ => rewrite <- prop_var_sub_prop_sub in H
   | |-  context [prop_sub [(svar _ _)] _ ] => rewrite <- prop_var_sub_prop_sub
   | H: good _ |- _ => unfold good in H; destruct H as [? ?] 
   | |- good _ => unfold good; split
   | H: closed [[ _ -> _ ]] |- _ => apply PImpl_keep_closed in H; destruct H as [? ?]
   | H: closed [[ _ /\ _ ]] |- _ => apply PAnd_keep_closed in H; destruct H as [? ?]
   | H: closed [[ _ \/ _ ]] |- _ => apply POr_keep_closed in H; destruct H as [? ?]
   | H: closed [[ _ <-> _ ]] |- _ => apply PIff_keep_closed in H; destruct H as [? ?]
   | H: closed [[∀_ ,_  ]] |- _ => apply PForall_keep_closed 
   | H: closed [[∃ _, _ ]] |- _ => apply PExists_keep_closed
   | H: closed [[ ¬  _ ]] |- _ => apply PNot_keep_closed 
   | |- closed [[ _ -> _ ]]  => apply PImpl_keep_closed; split
   | |- closed [[ _ /\ _ ]] => apply PAnd_keep_closed; split
   | |- closed [[ _ \/ _ ]]  => apply POr_keep_closed; split
   | |- closed [[ _ <-> _ ]]  => apply PIff_keep_closed; split
   | |- closed [[∀_ ,_  ]] => apply PForall_keep_closed
   | |- closed [[∃ _, _ ]] => apply PExists_keep_closed
   | |- closed [[ ¬  _ ]] => apply PNot_keep_closed
   | |- closed (prop_var_sub _ _) =>apply prop_var_sub_keep_closed
   | H: pred_legal [[¬ _ ]] _ |- _=> inversion H; subst; clear H
   | H: pred_legal [[_ /\ _]] _ |- _ => inversion H; subst; clear H
   | H: pred_legal [[_ \/ _]] _ |- _ => inversion H; subst; clear H
   | H: pred_legal [[ _ -> _ ]] _ |- _ => inversion H; subst; clear H
   | H: pred_legal [[_ <-> _]] _ |- _ => inversion H; subst; clear H
   | H: pred_legal [[∀ _ ,  _]] _ |- _ => inversion H; subst; clear H
   | H: pred_legal [[∃ _ , _]] _ |-_ => inversion H; subst; clear H
   | |- pred_legal [[¬ _ ]] _ => constructor
   | |- pred_legal [[_ /\ _]] _ => constructor
   | |- pred_legal [[_ \/ _]] _ => constructor
   | |- pred_legal [[ _ -> _ ]] _  => constructor
   | |- pred_legal [[_ <-> _]] _ => constructor
   | |- pred_legal [[∀ _ ,  _]] _ => constructor
   | |- pred_legal [[∃ _ , _]] _ => constructor
   | |- pred_legal (prop_var_sub _ _) _ =>apply prop_var_sub_keep_pred_legal
  end).   

(* ***************************************************************** *)
(*                                                    *)
(*                                                                   *)
(* Proof Rules                                                 *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Definition subset_def:= R.default.

Notation "t1 '⊆' t2" := (PAtom (AApp (AApp (APred subset_def) t1) t2) )(in custom sset at level 20, no associativity): Sugar_scope. 
(*  [[  ( ∀ _z, _z ∈ _x -> _z ∈ _y ) ]] *)

Definition is_empty_def:= R.next_name subset_def.
 (* [[ (∀ _y, ¬ _y ∈ _x) *)

Notation " 'is_empty'  t1":= (PAtom (AApp (APred is_empty_def) t1 )) (in custom sset at level 20, t1 at level 15,no associativity): Sugar_scope. 

(* t1 = {t2} *)
Definition is_singleton_def:= R.next_name is_empty_def.
(* [[ (∀ _z, _z ∈ _x <-> _z = _y) ]]. *)
 
Notation " 'is_singleton'  t1 t2 ":=  (PAtom (AApp (AApp (APred is_singleton_def) t1) t2) ) (in custom sset at level 20, t1 at level 15, t2 at level 15, no associativity): Sugar_scope. 

(* t1 = {t2, t3} *)
Definition has_two_ele_def:= R.next_name is_singleton_def.
Notation " 'is_empty'  t1":= (PAtom (AApp (APred is_empty_def) t1 )) (in custom sset at level 20, t1 at level 15,no associativity): Sugar_scope. 
 (*[[ (∀ _u, _u ∈ _x <-> _u = _y \/ _u = _z) ]]*)

Notation " 'has_two_ele'  t1 t2 t3":= (PAtom (AApp (AApp (AApp (APred has_two_ele_def) t1) t2) t3) ) (in custom sset at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity): Sugar_scope. 

(* t1 = (t2, t3) := {{t2}, {t2, t3}} *)
Definition is_pair_def:= R.next_name has_two_ele_def.
(*  [[ (∃ _u, ∃ _v, is_singleton _u _y  /\  has_two_ele _v _y _z/\ has_two_ele _x _u _v) ]]*)
  
Notation " 'is_pair'  t1 t2 t3":= (PAtom (AApp (AApp (AApp (APred is_pair_def) t1) t2) t3) ) (in custom sset at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity): Sugar_scope. 
 
(* t1 = t2 U t3 *)
Definition is_union2_def:= R.next_name is_pair_def.
(*[[ (∀ _u, _u  ∈ _x <-> _u ∈ _y \/ _u ∈ _z) ]] *)


Definition is_prod_def:= R.next_name is_union2_def.
 (*  [[(∀ _u, _u ∈ _x <-> ∃ _v, ∃ _w, _v ∈ _y /\ _w ∈ _z /\  is_pair _u _v _w ) ]]*)

Definition is_rel_def:= R.next_name is_prod_def.
(* [[ (∀ _u, _u ∈ _x -> ∃ _v, ∃ _w, _v ∈ _y /\ _w ∈ _z /\  is_pair _u _v _w)]] *)

(* (t1, t2) in t3 *)
Definition in_rel_def:= R.next_name is_rel_def.
 (* [[ (∃ _u,  is_pair _u _x _y  /\ _u ∈ _z) . *)
  
Notation " 'in_rel'  t1 t2 t3":= (PAtom (AApp (AApp (AApp (APred in_rel_def) t1) t2) t3) ) (in custom sset at level 20, t1 at level 15, t2 at level 15, t3 at level 15, no associativity): Sugar_scope. 

Definition is_func_def:= R.next_name in_rel_def.
(* [[ (∀ _y, ∀ _z, ∀ _u,  in_rel _y _z _x  -> in_rel _y _u _x  -> _z = _u) ]]. *)

Notation " 'is_func'  t1":=(PAtom (AApp (APred is_func_def) t1 ))  (in custom sset at level 20, t1 at level 15, no associativity): Sugar_scope. 

Definition is_inductive_def:= R.next_name is_func_def.
(* [[ (∅ ∈ _x /\ ∀ _y, (_y ∈ _x -> _y ∪ {_y} ∈ _x) ) ]] *)
 
Notation " 'is_inductive'  t1":= (PAtom (AApp (APred is_inductive_def) t1) ) (in custom sset at level 20, t1 at level 15, no associativity): Sugar_scope. 
 
Inductive provable:  prop -> Prop :=
| PForall_elim: forall (vr: V.t) (t: term) P,
    good P ->
    provable [[ (∀ vr, P) -> P [ vr |-> t] ]]
| PExists_intros: forall (vr: V.t) (t: term) P,
    good P ->
    provable [[ ( P [vr |-> t] ) -> (∃ vr, P) ]]
| PForall_intros: forall (vr: V.t) P Q,
    good P ->
    good Q ->
    free_occur vr P = 0 ->
    provable [[P -> Q]] ->
    provable [[P-> (∀vr, Q)]]
| PExists_elim: forall (vr: V.t) P Q,
    good P ->
    good Q ->
    free_occur vr Q = 0 ->
    provable [[P -> Q]] ->
    provable [[(∃vr,P) ->Q]]
| PAnd_intros: forall P Q,
    good P -> 
    good Q ->
    provable P ->
    provable Q ->
    provable [[P /\ Q]]
| PAnd_elim1: forall P Q,
    good P -> 
    good Q ->
    provable [[P /\ Q]] ->
    provable P
| PAnd_elim2: forall P Q,
    good P -> 
    good Q ->
    provable [[ P /\ Q]] ->
    provable Q
| POr_intros1: forall P Q,
    good P -> 
    good Q ->
    provable P ->
    provable [[P\/Q]]
| POr_intros2: forall P Q,
    good P -> 
    good Q ->
    provable Q ->
    provable [[P\/Q]]
| POr_elim: forall P Q R,
    good P -> 
    good Q ->
    good R ->
    provable [[P ->R]] ->
    provable [[Q-> R]] ->
    provable [[(P\/Q) -> R]]
| PNot_EM: forall P Q,
    good P -> 
    good Q ->
    provable [[P ->Q]] ->
    provable [[¬P -> Q]] ->
    provable Q
| PNot_Contra: forall P Q,
    good P -> 
    good Q ->
    provable [[¬P -> Q]] ->
    provable [[¬P -> ¬ Q]] ->
    provable P
| Assu: forall P,
    good P -> 
    provable [[P->P]]
| Modus_Ponens: forall P Q,
    good P -> 
    good Q ->
    provable [[P->Q]] ->
    provable P ->
    provable Q
| PImply_1: forall P Q,
    good P -> 
    good Q ->
    provable [[P->(Q->P)]]
| PImply_2: forall P Q R,
    good P -> 
    good Q ->
    good Q ->
    provable [[(P->Q->R) -> (P->Q) -> (P->R)]]
| PIff_intros: forall P Q,
    good P -> 
    good Q ->
    provable [[P -> Q]] ->
    provable [[Q -> P]] ->
    provable [[P <-> Q]]
| PIff_elim1: forall P Q,
    good P -> 
    good Q ->
    provable [[P <-> Q]] ->
    provable [[P -> Q]]
| PIff_elim2: forall P Q,
    good P -> 
    good Q ->
    provable [[P <-> Q]]->
    provable [[Q -> P]]
| PEq_refl: forall (t: term),
    provable [[t = t]]
| PEq_sub: forall P (x: V.t) (t t': term),
    good P ->
    provable [[t = t' -> P[x |-> t] -> P[x |-> t'] ]]
| PPredDef_elim: forall r xs P Q,
    good [[let r xs:= P in Q]] ->
    provable [[ Q[r|-> λ xs, P] ]] ->  
    provable [[ let r xs:= P in Q]]
| PPredDef_intros: forall r xs P Q,
    good [[let r xs:= P in Q]] ->
    provable [[ let r xs:= P in Q]] ->
    provable [[ Q[r|-> λ xs, P] ]]
| Empty:
    provable [[let is_empty_def ([_x]) := ∀ _y, ¬ _y ∈ _x in 
                     ( is_empty ∅) ]]
| Union:
    provable [[∀ _x, ∀ _y, ∀ _z, _z ∈ _x ∪ _y <-> _z ∈ _x \/ _z ∈ _y ]]
| Intersection_iff:
    provable [[∀ _x, ∀ _y, ∀ _z, _z ∈ _x ∩ _y <-> _z ∈ _x /\ _z ∈ _y ]]
| Singleton:
    provable [[∀ _x, ∀ _z, _z ∈ {_x} <-> _z = _x]] 
| Extensionality:
    provable [[∀ _x, ∀ _y, (∀ _z, _z ∈ _x <-> _z ∈ _y) <-> _x = _y]]
              
| Pairing:
    provable [[∀ _x, ∀ _y, ∃ _z, ∀ _u, _u ∈ _z <-> _u = _x \/ _u = _y]]
    
| Separation: forall  P,
    good P ->
    free_occur _x P = O ->
    free_occur _y P = O ->
    provable [[∀ _x, ∃ _y, ∀ _z, _z ∈ _y <-> _z ∈ _x /\ P]]

| Union_iff:
    provable [[∀ _x, ∃ _y, ∀ _z, _z ∈ _y <-> ∃ _u, _z ∈ _u /\ _u ∈ _x]]
                
| PowerSet:
    provable [[ let subset_def ([_x;_y]):=  ∀ _z, _z ∈ _x -> _z ∈ _y in
                    ∀ _x, ∃ _y, ∀ _z, _z ∈ _y <->_z ⊆_x]]

| Infinity:
    provable [[ let is_inductive_def ([_x]) := ∅ ∈ _x /\ ∀ _y, (_y ∈ _x -> _y ∪ {_y} ∈ _x) in
                     ∃ _x,  (is_inductive _x ) ]]

| Replacement: forall P,
    good P ->
    free_occur _z P = O ->
    free_occur _u P = O ->
    provable [[ (∀ _x, ∀ _y, ∀ _z, P [ _y |-> (var2tm _z) ] -> P -> _y = _z) ->
       (∀ _u, ∃ _z, ∀ _y, _y ∈ _z <-> ∃ _x, P /\ _x ∈ _u)]] 

| Choice:
    provable
      [[ let is_empty_def ([_x]) := ∀ _y, ¬ _y ∈ _x in 
          let is_singleton_def ([_x ; _y]) := ∀ _z, _z ∈ _x <-> _z = _y in
          let has_two_ele_def ([_x; _y; _z]) := ∀ _u, _u ∈ _x <-> _u = _y \/ _u = _z in
          let is_pair_def ([_x; _y; _z]) := ∃ _u, ∃ _v, (is_singleton _u _y)  /\  (has_two_ele _v _y _z) /\ (has_two_ele _x _u _v)  in
          let in_rel_def ([_x; _y; _z]) := ∃ _u,  (is_pair _u _x _y)  /\ _u ∈ _z in
          let is_func_def ([_x]) := ∀ _y, ∀ _z, ∀ _u,  (in_rel _y _z _x) -> (in_rel _y _u _x)  -> _z = _u in
          ∀ _x,
              (∀ _y, _y ∈ _x ->  ¬ (is_empty _y)) ->
              ∃ _y, is_func _y /\
                         ∀ _z, _z ∈ _x -> ∃ _u, in_rel _z _u _y /\ _u ∈ _z]]

| Regularity:
    provable
              [[ let is_empty_def ([_x]) := ∀ _y, ¬ _y ∈ _x in 
               ∀ _x, ¬ (is_empty _x) ->
                  ∃ _y, _y ∈ _x /\ ∀ _z, _z ∈ _x -> ¬ _z ∈ _y]]
                  
| Alpha_congruence: forall P Q,
   good P -> 
   good Q ->
   aeq P Q ->
   provable P -> 
   provable Q
.  

Theorem preddef_elim_provable: forall P,
  provable P ->
  provable (preddef_elim P).
Proof.
  intros. induction H; intros.
  + simpl_preddef_elim. pose proof PForall_elim vr t (preddef_elim P).
      eapply Alpha_congruence. 4: apply H0.
      - cgood.
      - cgood.
      - saeq.
      - cgood.
  + simpl_preddef_elim. pose proof PExists_intros vr t (preddef_elim P).
      eapply Alpha_congruence. 4: apply H0.
      - cgood.
      - cgood.
      - saeq.
      - cgood.
  +  simpl_preddef_elim. pose proof PForall_intros vr (preddef_elim P) (preddef_elim Q).
      eapply Alpha_congruence. 4: apply H3.
      - cgood.
      - cgood.
      - saeq.
      - cgood.
      - cgood.
      - apply legal_preddef_elim_keep_no_free_occur. cgood. easy.
      - now simpl_preddef_elim_in IHprovable. 
  +  simpl_preddef_elim. pose proof PExists_elim vr (preddef_elim P) (preddef_elim Q).
      eapply Alpha_congruence. 4: apply H3.
      - cgood.
      - cgood.
      - saeq.
      - cgood.
      - cgood.
      - apply legal_preddef_elim_keep_no_free_occur. cgood. easy.
      - now simpl_preddef_elim_in IHprovable.
  + simpl_preddef_elim. constructor; cgood.
  + simpl_preddef_elim. simpl_preddef_elim_in IHprovable.
      econstructor. cgood. 2: eauto. cgood.
  + simpl_preddef_elim. simpl_preddef_elim_in IHprovable.
      eapply PAnd_elim2. 3: eauto. cgood. cgood.
  + simpl_preddef_elim. constructor; cgood.
  + simpl_preddef_elim. apply POr_intros2; cgood.
  + simpl_preddef_elim. 
      simpl_preddef_elim_in IHprovable1. 
      simpl_preddef_elim_in IHprovable2. 
      constructor; cgood. 
  + simpl_preddef_elim. 
      simpl_preddef_elim_in IHprovable1. 
      simpl_preddef_elim_in IHprovable2. 
      eapply PNot_EM.  3: apply IHprovable1. 
      - cgood.
      - cgood.
      - easy.
  + simpl_preddef_elim. 
      simpl_preddef_elim_in IHprovable1. 
      simpl_preddef_elim_in IHprovable2.
      eapply PNot_Contra. 3: apply IHprovable1.
      - cgood.
      - cgood.
      - easy.
   + simpl_preddef_elim. constructor. cgood.
   + simpl_preddef_elim_in IHprovable1.
       eapply Modus_Ponens.
       3: apply IHprovable1.
       - cgood.
       - cgood.
       - easy.
   + simpl_preddef_elim. constructor; cgood.
   + simpl_preddef_elim. constructor; cgood.
   + simpl_preddef_elim. 
       simpl_preddef_elim_in IHprovable1. 
       simpl_preddef_elim_in IHprovable2. 
       constructor; cgood.
   + simpl_preddef_elim. 
       simpl_preddef_elim_in IHprovable.
       constructor; cgood.
   + simpl_preddef_elim. 
       simpl_preddef_elim_in IHprovable.
       apply PIff_elim2; cgood.
   + constructor.
   + simpl_preddef_elim.
       pose proof PEq_sub (preddef_elim P) x t t'.
       eapply Alpha_congruence.
       4: apply H0.
       - cgood. hnf. intros. easy. constructor.
       - cgood. hnf. intros. easy. constructor.
       - saeq.
       - cgood.
   + eapply Alpha_congruence.
       4: eauto.
       - cgood. apply preddef_unfold_keep_closed. cgood.
         apply preddef_unfold_keep_pred_legal. cgood.
       - cgood.
       - symmetry. now apply preddef_unfold_preddef_elim_aeq.
    + eapply Alpha_congruence.
       4: eauto.
       - cgood.
       - cgood. apply preddef_unfold_keep_closed. cgood.
         apply preddef_unfold_keep_pred_legal. cgood.
       - now apply preddef_unfold_preddef_elim_aeq.
    + pose proof Empty. apply PPredDef_intros in H.
        - easy.
        - now rewrite good_goodb.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + simpl_preddef_elim. constructor.
        - cgood.
        - apply legal_preddef_elim_keep_no_free_occur. cgood. easy.
        - apply legal_preddef_elim_keep_no_free_occur. cgood. easy.
   + constructor.
   + pose proof PowerSet. apply PPredDef_intros in H.
        - easy.
        - now rewrite good_goodb.
   + pose proof Infinity. apply PPredDef_intros in H.
        - easy.
        - now rewrite good_goodb.
   + simpl_preddef_elim.
       pose proof Replacement (preddef_elim P).
       eapply Alpha_congruence. 4: apply H2.
       - cgood. hnf. intros. easy. hnf. intros. easy. hnf. intros. easy.
         constructor. constructor. constructor.
       - cgood. hnf. intros. easy. hnf. intros. easy. hnf. intros. easy.
         constructor. constructor. constructor.
       - saeq. 
         * simpl_preddef_elim. saeq. 
         * simpl_preddef_elim. saeq. 
         * simpl_preddef_elim. saeq. 
       - cgood.
       - apply legal_preddef_elim_keep_no_free_occur. cgood.  easy.
       - apply legal_preddef_elim_keep_no_free_occur. cgood.  easy.     
   (**** Axiom of Choice: Repeat unfold the rule ****)
   + pose proof Choice.
       apply PPredDef_intros in H. 2: now rewrite good_goodb. cbv in H.
       apply PPredDef_intros in H. 2: now rewrite good_goodb. cbv in H.
       apply PPredDef_intros in H. 2: now rewrite good_goodb. cbv in H.
       apply PPredDef_intros in H. 2: now rewrite good_goodb. cbv in H.
       apply PPredDef_intros in H. 2: now rewrite good_goodb. cbv in H.
       apply PPredDef_intros in H. 2: now rewrite good_goodb. cbv in H.
       eapply Alpha_congruence. 4: apply H.
       - now rewrite good_goodb.
       - now rewrite good_goodb.
       - now rewrite aeq_aeqb.
  + pose proof Regularity.
      apply PPredDef_intros in H. 2: now rewrite good_goodb. easy.
  + eapply Alpha_congruence. 4: eauto.
      - cgood.
      - cgood.
      - now apply preddef_elim_aeq.
Qed.
   
Close Scope Sugar_scope.
End DemoSugar.
