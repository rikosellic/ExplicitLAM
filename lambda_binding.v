Require Import Coq.Lists.List.
Require Import FV.utils.
Require Import Coq.Sorting.Permutation.
Require Import Bool.
Require Import Compare_dec.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationClasses.
Require Import Operators_Properties.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.micromega.Lia.
Import ListNotations.

Module Type Naming_module_type.
Parameter C : Type.  (**  constant **)
Parameter V: Type. (**  variable, may have many types **)
Parameter VS: Type.
Parameter varsort: V -> VS. (**  A function that returns the variable's type **)
Parameter newvar: list V -> VS -> V. (**  Given a list of vars, return a var that is not in the list with given type **)
Axiom var_eq_dec:forall v1 v2: V, {v1 = v2} + {v1 <> v2}.
Axiom constant_eq_dec: forall v1 v2: C, {v1 = v2} + {v1 <> v2}.
Axiom newvar_fresh: forall (xs:list V) (v:VS), ~ In (newvar xs v) xs.
Axiom newvar_Permutation: forall (l1 l2:list V)(v:VS), Permutation l1 l2 -> newvar l1 v = newvar l2 v.
Axiom newvar_sort: forall xs T, varsort (newvar xs T) = T.

End Naming_module_type. 

Module General_lambda(Name:Naming_module_type).
Export Name. 

Corollary in_vars_dec: forall (x:V) xs, {In x xs} + {~In x xs}. 
Proof. intros. apply (in_dec var_eq_dec).  Qed. 

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(* Basic Definition                                           *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Inductive tm: Type:=
 | cons (c:C)
 | var (s:V)
 | app: tm -> tm -> tm
 | abs: V -> tm -> tm.

Coercion var : V >-> tm.
Coercion cons: C >-> tm.
Notation " 'λ' x . t" := (abs x t) (at level 22, no associativity, only printing).
Notation " M N":=(app M N)(at level 20, left associativity, only printing).

Fixpoint rank (t:tm):=
  match t with
  | cons c => 1
  | var s => 1
  | app t1 t2 => rank t1 + rank t2
  | abs s t0 => S (rank t0)
 end.

Lemma rank_positive: forall t,
  0<rank t.
Proof.
  induction t; simpl; try constructor.
  + apply PeanoNat.Nat.add_pos_r; tauto.
  + apply Lt.lt_le_S; tauto.
Qed.

Lemma lt_app_rank_l: forall t1 t2,
  rank t1 < rank (app t1 t2).
Proof.
  intros. simpl. apply PeanoNat.Nat.lt_add_pos_r. apply rank_positive.
Qed.

Lemma lt_app_rank_r: forall t1 t2,
  rank t2 < rank (app t1 t2).
Proof.
  intros. simpl. apply PeanoNat.Nat.lt_add_pos_l. apply rank_positive.
Qed.

Theorem rank_induction: forall P:tm -> Prop,
  (forall t, (forall x, rank x < rank t -> P x) -> P t) ->
  forall t, P t.
Proof.
  intros.
  assert (forall t n, rank t < n -> P t) as H_ind.
  { 
    intros. generalize dependent t0. induction n; intros.
    + inversion H0.
    + apply H. intros. apply IHn. apply Lt.lt_n_Sm_le in H0.
        inversion H0;subst. tauto.
        apply PeanoNat.Nat.lt_le_trans with (rank t0);tauto. 
  }
  intros. apply H_ind with (S (rank t)). constructor.
Qed.

Definition var_occur (x:V)(s:V):nat:=
 if var_eq_dec x s then (S O) else O.

Fixpoint free_occur (x:V)(t:tm):nat:=
 match t with
 | var s => var_occur x s
 | app t1 t2 => free_occur x t1 + (free_occur x t2)
 | abs s t0 => if var_eq_dec x s then O else free_occur x t0
 | cons c => O
end.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Substitution                                               *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)
Definition subst_task: Type := list (V*tm).

Definition domain (st:subst_task): list V:=
  map fst st.
  
Definition range (st:subst_task): list tm:=
  map snd st.

Definition distinct (st:subst_task):=
  NoDup (domain st).

Fixpoint st_occur (x:V)(st:subst_task):nat:=
 match st with
 | nil=> O
 | (s,t)::st0 => var_occur x s + free_occur x t + st_occur x st0
 end.

Fixpoint st_tm_occur (x:V)(st:subst_task):nat:=
 match st with
 | nil=> O
 | (s,t)::st0 => free_occur x t + st_tm_occur x st0
 end.

Fixpoint var_sub (x:V)(st:subst_task):tm:=
 match st with
 | nil => x
 | (x',t')::st' => if var_eq_dec x x' then t' 
                         else var_sub x st'
 end.

Fixpoint tm_var (t:tm):list V:=
 match t with
 | var s => [s]
 | app t1 t2 => tm_var t1++tm_var t2
 | abs s t0 => s::(tm_var t0)
 | cons c => nil
end.

Definition task_var (st: subst_task):=
  flat_map (fun p => fst p :: tm_var (snd p)) st.

Definition reduce (x:V)(st:subst_task):=
  filter (fun p=> if var_eq_dec x (fst p) then false else true) st.

Fixpoint list_reduce (xs:list V)(st:subst_task):subst_task:=
  match xs with
  | nil => st
  | x::xs0 => reduce x (list_reduce xs0 st)
end.

Fixpoint subst (st:subst_task) (t:tm):tm:=
  match t with
  | var s => var_sub s st
  | cons c => cons c
  | app t1 t2 => app (subst st t1) (subst st t2)
  | abs x t1 => let st':= reduce x st in
                match st_tm_occur x st' with
                | O => abs x (subst st' t1)
                | _ =>  let x':= newvar (tm_var t++task_var st') (varsort x) in (**  Brand new var **)
                             abs x' (subst ((x,var x')::st') t1)
                end
end.


(**** Basic Lemmas About String and Substitution****)

Lemma var_occur_eq_dec: forall x y,
  var_occur x y = 1 <-> x = y.
Proof.
  split; intros ;[unfold var_occur in H|unfold var_occur]; destruct(var_eq_dec x y); congruence.
Qed.

Lemma var_occur_not_eq_dec: forall x y,
  var_occur x y = 0 <-> x <> y.
Proof.
  split; intros ;[unfold var_occur in H|unfold var_occur]; destruct(var_eq_dec x y); congruence.
Qed.
 
Lemma var_occur_eq: forall x y,
  nat_reflect (x=y) (var_occur x y).
Proof.
  intros. unfold var_occur. destruct (var_eq_dec x y);constructor; tauto.
Qed.  
  
(** Discuss name **)  
Ltac destruct_eq_dec:=
  simpl; repeat ( simpl st_tm_occur; simpl free_occur; match goal with
  | |- ?t = ?t => reflexivity
  | H: ?t = ?t |- _ => clear H
  | H: context [var_occur _ _] |- _ => unfold var_occur in H
  | |- context [var_occur _ _]  => unfold var_occur
  | |- context [if (var_eq_dec ?x ?x) then _ else _ ] => destruct (var_eq_dec x x);[|congruence]
  | H: ?x = ?y |- context [if (var_eq_dec ?x ?y) then _ else _ ] => destruct (var_eq_dec x y);[|congruence]
  | H: ?x = ?y |- context [if (var_eq_dec ?x ?y) then _ else _ ] => destruct (var_eq_dec x y);[|congruence]
  | H: ?x <> ?y |- context [if (var_eq_dec ?x ?y) then _ else _ ] => destruct (var_eq_dec x y);[congruence|]
  | H: ?y <> ?x |- context [if (var_eq_dec ?x ?y) then _ else _ ] => destruct (var_eq_dec x y);[congruence|]
  | |- context [if (var_eq_dec _ _) then _ else _] => destruct (var_eq_dec _ _);simpl;[subst|]
  | |- context [var_occur ?x ?y] => destruct (var_occur_eq x y);[subst|]
  | H: context [if (var_eq_dec ?x  ?y) then _ else _] |- _  => destruct (var_eq_dec x y) in H; subst; try congruence
  | H: ?x = 0 |- _ => rewrite H
  | |- _  => try tauto
  end).
  
Lemma var_sub_range: forall s st,
  In (var_sub s st) (range st) \/ var_sub s st = s.
Proof. induction st. now right. destruct a. destruct_eq_dec. Qed.

Lemma no_st_occur_zero_no_st_tm_occur: forall x st,
  st_occur x st = 0 -> st_tm_occur x st = 0.
Proof.
  intros. induction st ; try easy.
  destruct a as [s t]. simpl in *. zero_r H. 
Qed. 

Lemma reduce_no_st_tm_occur: forall x y st,
  st_tm_occur x st = 0 -> st_tm_occur x (reduce y st) = 0.
Proof.
  intros. induction st. reflexivity.
  destruct a. simpl in H. zero_r H.
  apply IHst in H0.  destruct_eq_dec. 
Qed.

Lemma reduce_app: forall x st st',
  reduce x (st++st') = reduce x st ++ reduce x st'.
Proof. intros. apply filter_app. Qed.
    
Lemma list_reduce_cons: forall x l st,
 reduce x (list_reduce l st) = list_reduce (x::l) st.
Proof. intros. easy. Qed.

Lemma task_var_app: forall st1 st2,
  task_var (st1++st2) =  task_var st1 ++ task_var st2.
Proof. intros. apply flat_map_app. Qed.

Lemma st_tm_occur_app: forall x st1 st2,
st_tm_occur x (st1++st2) = st_tm_occur x st1 + st_tm_occur x st2.
Proof.
  intros. induction st1.
  + easy. 
  + simpl. rewrite IHst1. destruct a. now rewrite <- Plus.plus_assoc_reverse.  
Qed.

Lemma domain_app: forall l1 l2,
  domain(l1++l2) = domain l1 ++ domain l2.
Proof. intros. apply map_app. Qed.

Lemma tm_var_eq: forall M N,
  (var M) = (var N) ->
  M = N.
Proof. intros. congruence. Qed.

Lemma Permutation_keep_distinct: forall l1 l2,
  Permutation l1 l2 ->
  distinct l1 ->
  distinct l2.
Proof.
  unfold distinct. intros.
  assert (Permutation (domain l1) (domain l2)).
  unfold domain. perm. eapply Permutation_NoDup;eauto.
Qed.

Lemma reduce_Permutation: forall st1 st2 x,
  Permutation st1 st2 ->
  Permutation (reduce x st1) (reduce x st2).
Proof.
  intros. induction H.
  + constructor.
  + destruct x0 as [x0 t0].  destruct_eq_dec. perm. 
  + destruct  x0 as [x0 t0]. destruct y as [x1 t1]. simpl. destruct_eq_dec; perm. 
  + perm.
Qed.

Lemma list_reduce_Permutation: forall st1 st2 xs,
  Permutation st1 st2 ->
  Permutation (list_reduce xs st1) (list_reduce xs st2).
Proof. intros. induction xs. easy. now apply reduce_Permutation. Qed.

Lemma st_tm_occur_Permutation: forall st1 st2 x,
  Permutation st1 st2 ->
  st_tm_occur x st1 = st_tm_occur x st2.
Proof.
  intros. induction H.
  + reflexivity.
  + simpl. rewrite IHPermutation. reflexivity.
  + destruct x0 as [x0 t0]. destruct y as [x1 t1].
      simpl. now rewrite PeanoNat.Nat.add_shuffle3. 
  + congruence. 
Qed.

Lemma task_var_Permutation: forall st1 st2,
  Permutation st1 st2 ->
  Permutation (task_var st1) (task_var st2).
Proof.
  intros. induction H.
  + constructor.
  + destruct x as [x t]. simpl. perm. 
  + destruct x. destruct y. simpl. perm. 
  + perm.
Qed.

Lemma not_in_tm_var_no_free_occur: forall x t,
  ~ In x (tm_var t) -> free_occur x t = 0.
Proof.
  induction t; intros; simpl in H.
  + reflexivity.
  + destruct_eq_dec. 
  + des_notin H. simpl. rewrite IHt1; tauto. 
  + des_notin H. destruct_eq_dec.
Qed.
   

Lemma not_in_task_var_no_st_occur: forall x st,
  ~ In x (task_var st) -> st_occur x st =0.
Proof.
  induction st; intros. easy. 
  destruct a.  des_notin H. 
  apply not_in_tm_var_no_free_occur in H0. 
  simpl. rewrite H0. destruct_eq_dec.
Qed.

Lemma no_reduce: forall x st,
 ~ In x (domain st) ->
 reduce x st = st.
Proof. intros. induction st; try easy. destruct a.  des_notin H. destruct_eq_dec. f_equal. tauto. Qed.
    
Lemma not_in_domain_reduce_other : forall x x0 st, 
  x<>x0 -> 
  ~ In x0 (domain st) -> 
  ~ In x0 (domain (reduce x st)).
Proof. intros. induction st. easy. destruct a as [x1 t1]. des_notin H0. destruct_eq_dec. Qed.

Lemma not_in_task_var_not_in_reduced_task_var: forall x y st,
  ~ In x (task_var st) ->
  ~ In x (task_var (reduce y st)).
Proof.
  intros. induction st.
  + easy.
  + destruct a. des_notin H.  destruct_eq_dec.
    apply deMorgan2. split;[tauto|]. apply not_in_app. tauto. 
Qed.

Lemma reduce_swap: forall x y st,
  reduce x (reduce y st) = reduce y (reduce x st).
Proof.  induction st. easy. destruct a as [s t].  destruct_eq_dec.  now rewrite IHst. Qed.

Lemma reduce_list_reduce_swap: forall x xs st,
  reduce x (list_reduce xs st) = list_reduce xs (reduce x st).
Proof.
  intros. induction xs.
  + easy. 
  + simpl. rewrite <- IHxs. apply reduce_swap.
Qed.

Lemma reduce_distinct: forall st x,
  distinct st ->
  distinct (reduce x st).
Proof.
  unfold distinct.
  intros. induction st.
  + constructor.
  + destruct a as [x0 t0]. simpl.  destruct_eq_dec.
      - apply IHst. simpl in H. now rewrite NoDup_cons_iff in H. 
      - simpl in H. apply NoDup_cons. 
        * rewrite NoDup_cons_iff in H. destruct H.
           apply not_in_domain_reduce_other;tauto.
        * apply IHst. rewrite NoDup_cons_iff in H. tauto.
Qed.

    
(* Lemma NoDup_app: forall (l1 l2:list Str),
  NoDup l1 ->
  NoDup l2 ->
  (forall x , ~ In x l1 \/ ~ In x l2) ->
  NoDup (l1++l2).
Proof.
  intros. induction l1. tauto.
  assert (H2:=H1). specialize H2 with a. destruct H2.
  simpl in H2. apply deMorgan1 in H2. destruct H2. congruence.
  simpl. rewrite NoDup_cons_iff. split.
  + rewrite NoDup_cons_iff in H. destruct H. apply not_in_app. tauto.
  + apply IHl1.
     - rewrite NoDup_cons_iff in H. tauto.
     - intro. specialize H1 with x. destruct H1;try tauto.
       left. rewrite not_in_cons in H1. tauto.
Qed. *)

Lemma not_in_Forall: forall (x:V) l,
  ~ In x l <-> Forall (fun s => var_occur x s = 0) l.
Proof.
  split; intros.
  + rewrite Forall_forall. intros. destruct_eq_dec.
  + rewrite Forall_forall in H. induction l. easy. apply not_in_cons. split.
      - specialize H with a. destruct_eq_dec. 
        cut (1=0).
        * intros. discriminate.
        * apply H. now left.
      - apply IHl. intros. apply H. now right.
Qed.
     
Lemma not_in_domain_reduce_self: forall x st,
~ In x (domain (reduce x st)).
Proof. induction st. easy.  destruct a. destruct_eq_dec.  now apply not_in_cons. Qed.
    
Lemma not_in_domain_list_reduce_containing_self:forall x l st,
  In x l ->
  ~ In x (domain (list_reduce l st)).
Proof.
  intros. induction l.
  + inversion H.
  + simpl. destruct (var_eq_dec x a).
      - subst a. apply not_in_domain_reduce_self.
      - destruct H;try congruence. apply not_in_domain_reduce_other;[congruence|tauto].
Qed.
  
Lemma in_reduce_domain: forall (x y:V) st,
  In x (domain (reduce y st))  ->
  In x (domain st) /\ x<>y.
Proof.
  intros. destruct (var_eq_dec x y).
  + subst x. pose proof not_in_domain_reduce_self y st. contradiction.
  + split;[|exact n]. induction st.
      - inversion H.
      - destruct a. simpl in *. destruct_eq_dec. simpl in H. tauto.
Qed.
  
Lemma reduce_and_add_same_var_keep_distinct: forall x t st,
 distinct st ->
 distinct ((x,t)::(reduce x st)). 
Proof.
  unfold distinct. intros. simpl.
  induction st.
  + simpl. constructor;[tauto|constructor].
  + destruct a. simpl. destruct_eq_dec; simpl in H.
      - rewrite NoDup_cons_iff in H. tauto.
      - simpl. rewrite NoDup_cons_iff in H. destruct H.
        apply IHst in H0. rewrite NoDup_cons_iff in H0.
        apply NoDup_cons. rewrite not_in_cons. tauto.
        apply NoDup_cons. 2:tauto.
        clear H0 IHst. induction st.
        easy. destruct a. des_notin H. destruct_eq_dec. 
Qed.

Lemma distinct_cons_iff: forall x t st,
  distinct ((x,t)::st) <->
  ~ In x (domain st) /\ distinct st.
Proof. unfold distinct. intros. simpl. now rewrite NoDup_cons_iff. Qed.
   
(**  Tactic that deals with occurence **)   
Ltac solve_notin:=
  try match goal with
  | |- free_occur _ _ = 0 => apply not_in_tm_var_no_free_occur
  | |- st_tm_occur _ _ = 0 => apply no_st_occur_zero_no_st_tm_occur; apply not_in_task_var_no_st_occur
  | |- st_occur _ _ = 0 => apply not_in_task_var_no_st_occur
  end;
  try match goal with    
  | H:?z = newvar ?a ?b |- ~ In ?z _ => let H' := fresh "newvar_fresh" in pose proof newvar_fresh as H';
                                                                              rewrite H; specialize H' with a b
  | H:?z = newvar ?a ?b |-  ?z <> _ => let H' := fresh "newvar_fresh" in pose proof newvar_fresh as H';
                                                                              rewrite H; specialize H' with a b
  | H:?z = newvar ?a ?b |-  _ <> ?z => let H' := fresh "newvar_fresh" in pose proof newvar_fresh as H';
                                                                              rewrite H; specialize H' with a b
  | |- ~ In (newvar ?a ?b) _  => let H' := fresh "newvar_fresh" in pose proof newvar_fresh as H'; specialize H' with a b
  | |- _ <> newvar ?a ?b => let H' := fresh "newvar_fresh" in pose proof newvar_fresh as H'; specialize H' with a b
  | |-  newvar ?a ?b <> _ =>  let H' := fresh "newvar_fresh" in pose proof newvar_fresh as H'; specialize H' with a b
  end;
(*  try repeat  match goal with *)
  try repeat ( simpl in *;  match goal with
  | H: ~ In _ (_::_) |- _  => des_notin H
  | H: ~ In _ (_++_) |- _  => des_notin H
  | H: ~ (_ \/ _) |- _ => des_notin H
  | H: context[task_var (_ ++ _) ] |- _ => rewrite task_var_app in H
  | H: context[task_var [(?x,?t)]] |- _ => simpl task_var in H 
  | H: context [reduce _ (_++_)] |- _ => rewrite reduce_app in H
  | H: ?x <> ?x |- _ => congruence
  end);
  try repeat match goal with
  | H: context[Name.newvar] |- _ => fold newvar in H
  end;
  try repeat match goal with
  | |- context[task_var (_++_)] => rewrite task_var_app
  | |- context[task_var [(?x,?t)] ] => unfold task_var
  | |- context [reduce _ (_++_)] => rewrite reduce_app
  | |- context [list_reduce (?x::_) _]  => rewrite <- list_reduce_cons
  | |- ~ (_\/_) => apply deMorgan2; split
  | |- ~ In _ (task_var ((?x,?t)::?l))=> apply deMorgan2; split
  | |- ~ In _ (_::_) => apply not_in_cons; split
  | |- ~ In _ (_++_)  => apply not_in_app; split
  | |- ~ In _ _  => tauto
  | _ => try congruence; tauto
  end.   
   
Lemma str_not_in_domain_then_var_sub_is_self: forall s st,
 ~ In s (domain st) ->
 var_sub s st = s.
Proof. intros. induction st. easy. destruct a. des_notin H. destruct_eq_dec. Qed.

Corollary var_sub_with_task_reduce_self: forall s st,
  var_sub s (reduce s st) = s.
Proof. intros. apply str_not_in_domain_then_var_sub_is_self. apply not_in_domain_reduce_self. Qed.

Lemma var_sub_with_task_reduce_other: forall s x st,
  s <> x ->
  var_sub s st = var_sub s (reduce x st).
Proof. intros. induction st. easy. destruct a. repeat destruct_eq_dec. Qed.

Lemma var_sub_with_task_list_reduce_not_containing_self: forall xs st (x:V),
 ~ In x xs ->
 subst st x = subst (list_reduce xs st) x.
Proof.
  intros. induction xs.
  + reflexivity.
  + simpl. des_notin H.  apply IHxs in H0. clear IHxs. simpl in H0.
      pose proof var_sub_with_task_reduce_other x a (list_reduce xs st).
      rewrite <- H1. tauto. congruence.
Qed.

Lemma list_reduce_cons_with_var_in_reduced_list: forall x t xs st,
  In x xs ->
  list_reduce xs ((x,t)::st) = list_reduce xs st.
Proof.
  intros. induction xs as [|s xs ?].
  + inversion H.
  + destruct H. subst x. simpl. rewrite reduce_list_reduce_swap.
      destruct_eq_dec. now rewrite reduce_list_reduce_swap. 
      simpl. f_equal. tauto.
Qed.

Lemma list_reduce_cons_with_var_not_in_reduced_list: forall x t xs st,
  ~ In x xs ->
  list_reduce xs ((x,t)::st) = (x,t)::list_reduce xs st.
Proof.
  induction xs; intros.
  + easy.
  + des_notin H. simpl. rewrite IHxs; try easy. destruct_eq_dec. 
Qed. 
      
Theorem subst_exchangebale: forall st1 st2 t,
  distinct st1 ->
  Permutation st1 st2 ->
  subst st1 t = subst st2 t.
Proof.
  intros. generalize dependent st2. 
  generalize dependent st1.
  induction t; intros.
  + easy.
  + induction H0;subst.
      - easy.
      - destruct x. destruct_eq_dec. apply distinct_cons_iff in H. tauto.
      - destruct x. destruct y. destruct_eq_dec. unfold distinct in H.
         simpl in H. inversion H; subst. des_notin H2. congruence. 
      - assert (H0:=H). apply IHPermutation1 in H0. clear IHPermutation1.
        assert (distinct l'). apply Permutation_keep_distinct with l;tauto.
        apply IHPermutation2 in H1. congruence.
   + simpl. erewrite IHt1;eauto. erewrite IHt2; eauto.
   + simpl. assert (st_tm_occur v (reduce v st1) = st_tm_occur v (reduce v st2)). 
       apply st_tm_occur_Permutation. now apply reduce_Permutation.
       rewrite <- H1. destruct (st_tm_occur v (reduce v st1)).
      - specialize IHt with (reduce v st1) (reduce v st2).
        rewrite IHt; try easy. now apply reduce_distinct. now apply reduce_Permutation.
      - specialize IHt with ((v, var (newvar (v :: tm_var t ++ task_var (reduce v st1)) (varsort v))) :: reduce v st1)
          ((v, var (newvar (v ::  tm_var t ++ task_var (reduce v st2)) (varsort v))) :: reduce v st2).
        rewrite IHt.
        * assert (newvar (v :: tm_var t ++ task_var (reduce v st1)) (varsort v) = newvar (v :: tm_var t ++ task_var (reduce v st2) ) (varsort v)).
           apply newvar_Permutation. perm. 
           apply task_var_Permutation. apply reduce_Permutation. tauto. now rewrite H2. 
       * apply reduce_and_add_same_var_keep_distinct; tauto.
       * assert (newvar (v :: tm_var t ++ task_var (reduce v st1)) (varsort v)= newvar (v :: tm_var t ++ task_var (reduce v st2)) (varsort v)).
          apply newvar_Permutation. perm. 
          apply task_var_Permutation. now apply reduce_Permutation.
          rewrite H2. constructor. now apply reduce_Permutation.
Qed.     

Lemma subst_nil: forall t, subst [] t = t.
Proof. induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; congruence. Qed.

Lemma subst_var_with_itself: forall s t, subst [(s,var s)] t = t.
Proof.
  induction t; destruct_eq_dec; try congruence.
  + now rewrite subst_nil. 
  + simpl. congruence.  
Qed. 

Lemma var_sub_keep_no_occur: forall x (s:V) st,
  s <> x ->
  st_tm_occur s st = 0 ->
  free_occur s (subst st x) = 0.
Proof.  intros. induction st. destruct_eq_dec. destruct a.  zero_r H0. destruct_eq_dec. Qed. 

Corollary var_sub_keep_no_occur_st_occur: forall x s st,
  s<>x ->
  st_occur s st = 0 ->
  free_occur s (subst st x) =0.
Proof. intros. apply no_st_occur_zero_no_st_tm_occur in H0.  now apply var_sub_keep_no_occur. Qed.

Corollary var_sub_keep_no_occur_task_var: forall x s st,
  s<>x ->
  ~ In s (task_var st) ->
  free_occur s (subst st x) = 0.
Proof. intros. apply not_in_task_var_no_st_occur in H0. now apply var_sub_keep_no_occur_st_occur. Qed.

Lemma var_sub_with_var_not_in_app_domain_l: forall st1 st2 (x:V),
  ~ In x (domain st1) ->
  subst (st1++st2) x = subst st2 x.
Proof.
  intros. induction st1.
  + easy.
  + destruct a. des_notin H. destruct_eq_dec. 
Qed.

Lemma var_sub_with_var_not_in_app_domain_r: forall st1 st2 (x:V),
  ~In x (domain st2) ->
  subst (st1++st2) x = subst st1 x.
Proof.
  intros. induction st1.
  + simpl. now apply str_not_in_domain_then_var_sub_is_self.
  + destruct a. destruct_eq_dec. 
Qed.


Lemma subst_reduce_swap_varong: forall x t l1 l2 xs l M,
  subst ( l++ list_reduce xs (reduce x l1 ++ (x,t)::l2)) M = subst ( l ++ list_reduce xs ((x,t)::(reduce x l1)++l2)) M.
Proof.
  intros. revert x t l1 l2 xs l. induction M; intros.
  + easy.
  + destruct (in_vars_dec s (domain l)).
      - induction l as [|u us IHl].
        * simpl in i. tauto.
        * destruct u. simpl in i. destruct i; subst; destruct_eq_dec.
      - rewrite 2 var_sub_with_var_not_in_app_domain_l; try tauto.
        induction l1.
        * easy. 
        * destruct a. simpl.
           destruct_eq_dec.  destruct (in_vars_dec x xs); destruct (in_vars_dec v xs). 
           ++ repeat rewrite list_reduce_cons_with_var_in_reduced_list; try tauto.
                  rewrite  list_reduce_cons_with_var_in_reduced_list in IHl1;tauto.
           ++ rewrite list_reduce_cons_with_var_not_in_reduced_list; try tauto.
                  rewrite list_reduce_cons_with_var_in_reduced_list; try tauto.
                  rewrite list_reduce_cons_with_var_not_in_reduced_list; try tauto.
                  simpl. destruct_eq_dec.  rewrite list_reduce_cons_with_var_in_reduced_list in IHl1;tauto.
           ++ rewrite list_reduce_cons_with_var_in_reduced_list; try tauto.
                  rewrite list_reduce_cons_with_var_not_in_reduced_list; try tauto.
                  rewrite list_reduce_cons_with_var_in_reduced_list; try tauto.
                  rewrite list_reduce_cons_with_var_not_in_reduced_list in IHl1; try tauto.
           ++ repeat rewrite list_reduce_cons_with_var_not_in_reduced_list; try tauto.
                  rewrite list_reduce_cons_with_var_not_in_reduced_list in IHl1; try tauto.
                  simpl in *. destruct_eq_dec.
  + simpl. rewrite IHM1. now rewrite IHM2. 
  + unfold subst. 
      assert (st_tm_occur v (reduce v (l++ list_reduce xs (reduce x l1 ++ (x, t) :: l2))) =  
      st_tm_occur v (reduce v (l ++ list_reduce xs ((x, t) :: reduce x l1 ++ l2)))).
      { apply st_tm_occur_Permutation. apply reduce_Permutation. perm. 
         apply list_reduce_Permutation. symmetry. apply Permutation_middle. }
     rewrite <- H.  destruct (st_tm_occur v (reduce v (l++ list_reduce xs (reduce x l1 ++ (x, t) :: l2)))); fold subst.
     - f_equal. rewrite 2 reduce_app. rewrite 2 list_reduce_cons. apply IHM.
     - assert (newvar (tm_var (abs v M) ++ task_var (reduce v (l ++ list_reduce xs (reduce x l1 ++ (x, t) :: l2))))
     (varsort v)=newvar (tm_var (abs v M) ++ task_var (reduce v (l ++ list_reduce xs ((x, t) :: reduce x l1 ++ l2))))
     (varsort v)). 
     { apply newvar_Permutation. perm. apply task_var_Permutation.
     apply reduce_Permutation. apply Permutation_app_head. apply list_reduce_Permutation. symmetry. apply Permutation_middle.
     }
     rewrite H0. remember (newvar
       (tm_var (abs v M) ++
        task_var (reduce v (l ++ list_reduce xs ((x, t) :: reduce x l1 ++ l2)))) 
       (varsort v)) as z. clear H0. f_equal. rewrite 2 reduce_app. rewrite 2 list_reduce_cons.
     specialize IHM with x t l1 l2 (v::xs) ((v, var z) :: reduce v l). tauto.
 Qed.
 
Corollary subst_reduce_swap: forall x t l1 l2 M,
   subst  (reduce x l1 ++ (x,t)::l2) M = subst ((x,t)::(reduce x l1)++l2) M.
Proof. intros. apply subst_reduce_swap_varong  with (xs:=nil) (l:=nil). Qed.

Lemma subst_keep_no_free_occur: forall x st M,
  st_tm_occur x st = 0 ->
  free_occur x M = 0 ->
  free_occur x (subst st M) = 0.
Proof.
  intros. generalize dependent st. induction M;intros.
  + reflexivity.
  + simpl in H0. rewrite var_occur_not_eq_dec in H0.  now apply var_sub_keep_no_occur.
  + simpl.  zero_r H0.  rewrite IHM1; try tauto. now rewrite IHM2.
  + simpl.  simpl in H0. destruct (st_tm_occur v (reduce v st)) eqn:E.
      - destruct_eq_dec. apply IHM. tauto.  now apply reduce_no_st_tm_occur.
      - destruct_eq_dec.
         * apply reduce_no_st_tm_occur with v v st in H.
            rewrite H in E. discriminate. 
         * apply IHM. easy.
            simpl. rewrite <- var_occur_not_eq_dec in n1. rewrite n1.
            simpl. now apply reduce_no_st_tm_occur. 
Qed.

Corollary subst_one_term_keep_no_free_occur: forall x y M N,
  free_occur x M = 0 ->
  free_occur x N = 0 ->
  free_occur x (subst [(y, N)] M) = 0.
Proof. intros. apply subst_keep_no_free_occur. simpl. now rewrite H0. easy. Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Alpha Equivalence                                      *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Inductive is_var: tm -> Prop :=
 | str_is_var: forall s:V, is_var (var s).


(** Match binders at the same location, true means valid, false means it does not matter (not valid)**)
Definition binder_pair:Type:=V*V*bool.
Definition binder_list:Type:=list binder_pair.

Definition binder_update (x:V)(y:V)(bd:binder_pair):binder_pair:=
  let '(x0,y0,b):= bd in
  if zerop (var_occur x x0 + var_occur y y0) then bd else (x0,y0,false).

Definition update (x:V)(y:V)(st:binder_list):=
  map (fun bd => binder_update x y bd) st.

Definition binder_l (st:binder_list):list V:=
  map (fun x => fst (fst x)) st.

Definition binder_r (st:binder_list): list V:=
  map (fun x => snd (fst x)) st.

(** Parse the two terms from top to bottom, two terms are alpha equivalent if
 alpha_eq nil M N **)
Inductive alpha_eq: binder_list -> tm -> tm -> Prop:=
| cons_aeq: forall bd (c:C), alpha_eq bd c c
| str_aeq1: forall bd (s1 s2:V), (** Living binders **)
           varsort s1 = varsort s2 ->
           In (s1,s2, true) bd ->
           alpha_eq bd (var s1) (var s2)
| str_aeq2: forall bd (s:V), (** Not binder, free variable **)
           ~ In s (binder_l bd) ->
           ~ In s (binder_r bd) ->
           alpha_eq bd s s
| app_aeq: forall bd t1 t2 t3 t4,
           alpha_eq bd t1 t3 ->
           alpha_eq bd t2 t4 ->
           alpha_eq bd (app t1 t2)(app t3 t4)
| abs_aeq: forall x x' bd t1 t2, (** Record a new binder relation, clear invalid ones**)
           varsort x = varsort x' ->
           alpha_eq ((x, x', true)::(update x x' bd))  t1 t2 ->
           alpha_eq  bd (abs x t1)(abs x' t2)
. 

Definition aeq: relation tm:= fun t1 t2 => alpha_eq nil t1 t2.

Notation "x =a= y" := (aeq x y) (at level 42, no associativity).

Inductive valid_binder: binder_list -> Prop:=
| valid_nil: valid_binder nil
| valid_cons: forall x y l,
              varsort x = varsort y ->
              valid_binder l ->
              valid_binder ((x,y,true)::(update x y l))
.

Lemma irrelevant_update: forall (x y x0 y0:V) (b:bool) st, 
  x <> x0 /\ y <> y0 ->
  In (x,y,b) st <-> In (x,y,b) (update x0 y0 st).
Proof.
  split;intros.
  + induction st.
      - inversion H0.
      - destruct H0.
         * subst a. left. simpl.  assert(var_occur x0 x + var_occur y0 y=0).
            destruct H. destruct_eq_dec. now rewrite H0. 
         * right. tauto.
  + induction st. simpl in H0. tauto. 
      destruct H0. 
      - destruct a as [[x1 y1] b1]. unfold binder_update in H0. unfold var_occur in H0.
        destruct (var_eq_dec x0 x1); destruct (var_eq_dec y0 y1);simpl in H0; 
        try inversion H0; try subst; try destruct H; try congruence. now left.
      - right. tauto. 
Qed.   

Lemma binder_not_in_list_update_l: forall x y z st,
  ~ In (x,y,true) (update x z st).
Proof.
  induction st. easy.
  destruct a as [[s1 s2] b].
  simpl. unfold var_occur. 
  destruct (var_eq_dec x s1); destruct (var_eq_dec z s2);subst;simpl;apply deMorgan2;
  split;try congruence; tauto.
Qed.

Lemma binder_not_in_list_update_r: forall x y z st,
  ~ In (x,y,true) (update z y st).
Proof.
  induction st. tauto.
  destruct a as [[s1 s2] b].
  simpl. unfold var_occur. 
  destruct (var_eq_dec z s1); destruct (var_eq_dec y s2);subst;simpl;apply deMorgan2;
  split;try congruence; tauto.
Qed.

Lemma true_binder_in_updated_list: forall x y x0 y0 st,
  In (x,y,true) (update x0 y0 st) -> In (x,y,true) st /\ x<>x0 /\ y <> y0.
Proof.
  intros. induction st. inversion H.
  destruct a as [[s1 s2] b]. destruct H.
  simpl in H. unfold var_occur in H. destruct (var_eq_dec x0 s1); destruct (var_eq_dec y0 s2);
  subst;simpl in H;inversion H;subst.
  + split;[left;tauto|split;congruence].
  + apply IHst in H. split;[right;tauto|tauto].
Qed. 


(***This lemma is wrong!***)
(* Lemma valid_binder_false: forall x y st, 
  valid_binder st ->
  In (x,y,false) st -> (exists z, (In (x,z,true) st \/ In (z,y,true) st)). 
*)

Lemma valid_binder_injective_l: forall x y z st, 
valid_binder st ->
In (x,y,true) st -> In (x,z,true) st -> y=z.
Proof.
  intros. induction H. inversion H0.
  destruct H0;destruct H1.
  + inversion H0;inversion H1;subst. easy. 
  + inversion H0;subst. pose proof binder_not_in_list_update_l x z y l. contradiction.
  + inversion H1;subst. pose proof binder_not_in_list_update_l x y z l. contradiction.
  + apply true_binder_in_updated_list in H0. apply true_binder_in_updated_list in H1. tauto.  
Qed.

Lemma valid_binder_injective_r: forall x y z st,
valid_binder st ->
In (x,y,true) st -> In (z,y,true) st -> x=z.
Proof.
  intros. induction H. inversion H0.
  destruct H0;destruct H1.
  + inversion H0;inversion H1;subst. easy.
  + inversion H0;subst. pose proof binder_not_in_list_update_r z y x l. contradiction.
  + inversion H1;subst. pose proof binder_not_in_list_update_r x y z l. contradiction.
  + apply true_binder_in_updated_list in H0. apply true_binder_in_updated_list in H1. tauto.  
Qed.
 
Lemma update_valid: forall x y l,
  varsort x = varsort y ->
  valid_binder l ->
  valid_binder ((x,y,true)::(update x y l)).
Proof. intros. now constructor. Qed. 

Lemma update_length: forall x y st,
  length st = length (update x y st).
Proof.  induction st. easy. simpl. now rewrite IHst. Qed.
 
Lemma update_app: forall x y l1 l2,
  update x y (l1++l2) = update x y l1 ++ (update x y l2).
Proof. intros. apply map_app. Qed. 

Lemma binder_l_app: forall l1 l2,
  binder_l (l1++l2) = binder_l l1 ++ binder_l l2.
Proof. intros. apply map_app. Qed. 

Lemma binder_r_app: forall l1 l2,
  binder_r (l1++l2) = binder_r l1 ++ binder_r l2.
Proof. intros. apply map_app. Qed. 

Lemma in_binder_l: forall x y (b:bool) st,
  In (x, y ,b) st ->
  In x (binder_l st). 
Proof.
  intros. induction st.
  + inversion H.
  + destruct H. subst a. now left.
      destruct a. destruct p. simpl. tauto.
Qed.

Lemma in_binder_r: forall x y (b:bool) st,
  In (x, y, b) st ->
  In y (binder_r st). 
Proof.
  intros. induction st.
  + inversion H.
  + destruct H. subst a. now left.
      destruct a. destruct p. simpl. tauto.
Qed. 

Lemma update_binder_l: forall x y st,
  binder_l st = (binder_l (update x y st)).
Proof.
  induction st.
  + easy.
  + destruct a. destruct p. simpl. 
      destruct (var_occur x v + var_occur y v0); rewrite IHst;reflexivity.
Qed.

Lemma update_binder_r: forall x y st, 
  binder_r st = binder_r (update x y st).
Proof.
  induction st.
  + easy.
  + destruct a. destruct p. simpl.  
      destruct (var_occur x v + var_occur y v0); rewrite IHst; reflexivity. 
Qed.

Ltac shorten_update:=
  repeat match goal with
  | [|- context [binder_l (update ?x ?y ?l)]] => rewrite  <- update_binder_l
  | [|- context [binder_r (update ?x ?y ?l)]] => rewrite  <- update_binder_r
  | [|- context [length (update ?x ?y ?l)]] => rewrite <- update_length
  | [H: context [binder_l (update ?x ?y ?l)]|- _] => rewrite  <- update_binder_l in H
  | [H: context [binder_r (update ?x ?y ?l)]|- _] => rewrite  <- update_binder_r in H
  | [H: context [length (update ?x ?y ?l)]|- _] => rewrite <- update_length in H
  end.

(** Alpha reflexivity **)
Inductive same_binder: V* V * bool->Prop:=
| same_binder_constructor: forall (s:V) (b:bool), same_binder (s,s,b)
.
    
Lemma update_same_binder: forall s l,
  Forall same_binder l <->
  Forall same_binder (update s s l).
Proof.
  split;intros. 
  + induction l.
      - tauto.
      - destruct a. rewrite <- Forall_cons_iff in H.
        destruct H. inversion H; subst.
        simpl. destruct (var_occur s s0 + var_occur s s0); apply Forall_cons; try constructor;tauto.
  + induction l.
      - constructor.
      - destruct a as [[s1 s2] b].
        simpl in H. inversion H; subst. clear H.
        apply Forall_cons;[|tauto]. destruct (var_occur s s1 + var_occur s s2).
        * tauto.
        * inversion H2;subst. constructor.  
Qed.

Lemma same_binder_same_list: forall l,
  Forall same_binder l ->
  binder_l l =  binder_r l.
Proof.
  intros. induction l.
  + reflexivity.
  + rewrite <- Forall_cons_iff in H. destruct H.
      destruct a.  inversion H;subst. 
      apply IHl in H0. simpl. congruence.
Qed.
     
Lemma aeq_refl_varong: forall l t,
  Forall same_binder l ->
  valid_binder l ->
  alpha_eq l t t.
Proof.
  intros. generalize dependent l.  induction t;intros.
  + constructor.
  + induction H0.
      - now apply str_aeq2.
      - inversion H; subst. clear H. inversion H4;subst. clear H4.
        destruct (var_eq_dec y s).
        * subst y. apply str_aeq1. easy. now left.
        * apply update_same_binder in H5. apply IHvalid_binder in H5. clear IHvalid_binder.
           inversion H5;subst.
           ++ apply str_aeq1. easy. right. apply irrelevant_update;[split;congruence|tauto].
           ++ apply str_aeq2;simpl;apply deMorgan2;split;try congruence; shorten_update;tauto.
 + constructor; [apply IHt1;tauto| apply IHt2;tauto].
 + constructor. specialize IHt with ((v, v, true) :: update v v l). easy.
     apply IHt. apply Forall_cons. constructor. now apply update_same_binder.  now apply update_valid. 
Qed.  

Fact aeq_refl: Reflexive aeq.
Proof. unfold Reflexive. intros. apply aeq_refl_varong with (l:=nil); [apply Forall_nil| constructor]. Qed.  

(** Alpha Symmetry **)
Inductive sym_binder: binder_list -> binder_list -> Prop:=
 | sym_nil: sym_binder nil nil
 | sym_cons: forall x y b bd1 bd2,
      sym_binder bd1 bd2 ->
      sym_binder ((x,y,b)::bd1) ((y,x,b)::bd2).

Lemma in_sym_binder: forall x y b bd1 bd2,
  sym_binder bd1 bd2 ->
  In (x,y,b) bd1 <-> In (y,x,b) bd2.
Proof.
  intros. generalize dependent bd2. induction bd1; intros.
  + inversion H; subst. tauto.
  + split; intros.
      - inversion H0; subst;inversion H; subst.
        * now left.
        * right. specialize IHbd1 with bd3. tauto.
      - destruct bd2. inversion H0. inversion H0; subst.
        * inversion H; subst. now left.
        * right. specialize IHbd1 with bd2. inversion H; subst. tauto.
Qed.

Lemma sym_binder_l: forall bd1 bd2,
  sym_binder bd1 bd2 ->
  binder_l bd1 = binder_r bd2.
Proof.
  intros bd1. induction bd1; intros;inversion H; subst.
  + reflexivity.
  + inversion H; subst. simpl. specialize IHbd1 with bd3. rewrite IHbd1;tauto.
Qed.
   
Lemma sym_binder_r: forall bd1 bd2,
  sym_binder bd1 bd2 ->
  binder_r bd1 = binder_l bd2.
Proof.
  intros bd1. induction bd1; intros;inversion H; subst. 
  + reflexivity.
  + simpl. specialize IHbd1 with bd3. rewrite IHbd1;tauto.
Qed.   

Lemma sym_binder_update: forall x y bd1 bd2,
  sym_binder bd1 bd2 ->
  sym_binder ((x,y,true)::(update x y bd1)) ((y,x,true)::(update y x bd2)).
Proof.
  intros. induction H.
  + simpl. repeat constructor. 
  + inversion IHsym_binder; subst. constructor. simpl.
      destruct (var_occur_eq x x0);destruct (var_occur_eq y y0); simpl;constructor;tauto.  
Qed.

Lemma aeq_sym_varong: forall (l1 l2: binder_list) (t1 t2: tm),
  sym_binder l1 l2 ->
  alpha_eq l1 t1 t2 ->
  alpha_eq l2 t2 t1.
Proof.
  intros. generalize dependent l2. induction H0; intros.
  + constructor.
  + apply str_aeq1. easy. apply in_sym_binder with s1 s2 true bd l2 in H1. tauto. 
  + apply str_aeq2. rewrite <- sym_binder_r with bd l2;tauto.
    rewrite <- sym_binder_l with bd l2;tauto.
  + specialize IHalpha_eq1 with l2.  specialize IHalpha_eq2 with l2. constructor; tauto.
  + constructor. specialize IHalpha_eq with ((x', x, true) :: update x' x l2). easy.
     apply IHalpha_eq. apply sym_binder_update; tauto.
Qed.

Fact aeq_sym: Symmetric aeq.
Proof. unfold Symmetric. intros. apply aeq_sym_varong with (l1:=nil)(l2:=nil) ;[constructor|tauto]. Qed.

Inductive binder_var_equal: binder_list -> binder_list -> Prop:=
| nil_eq: binder_var_equal nil nil
| cons_eq: forall (x y:V) (b1 b2:bool) (xs ys:binder_list), 
            binder_var_equal xs ys ->
            binder_var_equal ((x,y,b1)::xs) ((x,y,b2)::ys).

(** Alpha transitivity **)  
Inductive trans_binder: binder_list -> binder_list -> binder_list -> Prop:=
| trans_nil: trans_binder nil nil nil
| trans_cons: forall x y z b1 b2 bd1 bd2 bd3,
  trans_binder bd1 bd2 bd3 ->
  trans_binder ((x,y,b1):: bd1) ((y,z,b2):: bd2) ((x,z,true):: (update x z bd3)).

Lemma trans_binder_var_equal: forall bd1 bd2 bd3 bd4 bd,
  binder_var_equal bd1 bd3 ->
  binder_var_equal bd2 bd4 ->
  trans_binder bd1 bd2 bd ->
  trans_binder bd3 bd4 bd.
Proof.
  intros. revert bd2 bd4 bd H0 H1. induction H; intros.
  + inversion H1; subst. inversion H0; subst. constructor.
  + inversion H1; subst. inversion H0; subst. constructor.
      specialize IHbinder_var_equal with bd0 ys0 bd3.
      inversion H1; subst. tauto.
Qed.

Lemma trans_common_binder: forall bd1 bd2 bd3,
  trans_binder bd1 bd2 bd3 ->
  binder_r bd1 = binder_l bd2.
Proof.  intros. induction H. reflexivity. simpl. congruence. Qed.

Lemma trans_result_binder_l: forall bd1 bd2 bd3,
  trans_binder bd1 bd2 bd3 ->
  binder_l bd1 = binder_l bd3.
Proof. intros. induction H. reflexivity. simpl. shorten_update. congruence. Qed.

Lemma trans_result_binder_r: forall bd1 bd2 bd3,
  trans_binder bd1 bd2 bd3 ->
  binder_r bd2 = binder_r bd3.
Proof.  intros. induction H. reflexivity. simpl. shorten_update. congruence. Qed.

Lemma irrelevant_var_aeq: forall l (s1 s2 x y: V),
  s1 <> x ->
  s2 <> y ->
  alpha_eq l s1 s2 <-> alpha_eq ((x,y,true)::(update x y l)) s1 s2.
Proof.
  split; intros.
  + inversion H1;subst.
      - apply str_aeq1. easy. right. now apply irrelevant_update.
      - apply str_aeq2; simpl; apply deMorgan2; split; try congruence;shorten_update;tauto.
  + inversion H1;subst.
      - apply str_aeq1. easy. destruct H6.
        * assert (x=s1) by congruence. congruence.
        * rewrite irrelevant_update. apply H2. tauto.
      - apply str_aeq2. 
        * des_notin H5. now shorten_update. 
        * des_notin H6. now shorten_update. 
Qed.

Lemma binder_var_equal_sym: forall bd1 bd2,
  binder_var_equal bd1 bd2 ->
  binder_var_equal bd2 bd1. 
Proof. intros. induction H; constructor;tauto. Qed.

Lemma update_var_equal: forall x y bd,
  binder_var_equal bd (update x y bd).
Proof.
  induction bd.
  + constructor.
  + destruct a as [[x' y'] b]. simpl. destruct(var_occur x x' + var_occur y y');constructor;tauto.
Qed.  

Lemma aeq_trans_varong: forall l1 l2 l3 t1 t2 t3,
  trans_binder l1 l2 l3 ->
  valid_binder l1 ->
  valid_binder l2 ->
  alpha_eq l1 t1 t2 ->
  alpha_eq l2 t2 t3 ->
  alpha_eq l3 t1 t3.
Proof.
  intros. revert l2 l3 t3 H H1 H3. induction H2; intros.
  + inversion H3; subst. constructor.
  + revert l2 l3 t3 H2 H3 H4. induction H0. inversion H1.
      simpl in H1. intros. inversion H5;subst.
      - destruct H1.
        * apply str_aeq1. congruence. injection H1 as H1.
           subst x. subst y. inversion H3;subst. inversion H4; subst.
           destruct H9. injection H1 as H1. subst s3.  now left. 
           apply true_binder_in_updated_list in H1. destruct H1 as [_ [? _]]. congruence. 
        * assert (s1 <> x /\ s2 <> y). pose proof true_binder_in_updated_list s1 s2 x y l.
           now apply H6. destruct H6.
           inversion H3; subst. inversion H4;subst. destruct H9. congruence. 
           apply true_binder_in_updated_list in H9. apply irrelevant_var_aeq;[easy..|].
           apply true_binder_in_updated_list in H1. destruct H1 as [H1 _]. eapply IHvalid_binder.
           easy. pose proof trans_binder_var_equal (update x y l) (update y z l0) l l0 bd3.
           apply H10 in H16. apply H16.
           apply binder_var_equal_sym. apply update_var_equal.
           apply binder_var_equal_sym. apply update_var_equal.  
           easy. now apply irrelevant_var_aeq in H5. 
      - destruct H1. 
        * injection H1 as H1.  subst x. subst y. inversion H3; subst. simpl in H7. tauto.
        * inversion H3;subst. apply in_binder_r in H1. 
           rewrite trans_common_binder with (update x y l) bd2 bd3 in H1. des_notin H7.  tauto. easy.
 + inversion H4; subst. 
      - apply in_binder_l in H8. rewrite trans_common_binder with bd l2 l3 in H1;tauto. 
      - apply str_aeq2. rewrite <- trans_result_binder_l with bd l2 l3;tauto.
         rewrite <- trans_result_binder_r with bd l2 l3; tauto.
 + inversion H3; subst. constructor.
     specialize IHalpha_eq1 with l2 l3 t7. apply IHalpha_eq1; tauto.
     specialize IHalpha_eq2 with l2 l3 t8. apply IHalpha_eq2; tauto.
 + inversion H4; subst. constructor. congruence.
     specialize IHalpha_eq with ((x', x'0, true) :: update x' x'0 l2)  ((x, x'0, true) :: update x x'0 l3) t4. 
     apply IHalpha_eq; try tauto. constructor. easy. easy. constructor.
     pose proof trans_binder_var_equal bd l2 (update x x' bd) (update x' x'0 l2) l3.
     apply H5 in H1. tauto. apply update_var_equal. apply update_var_equal. now constructor.
Qed.

Fact aeq_trans: Transitive aeq.
Proof. unfold Transitive. intros. apply aeq_trans_varong with (l1:=nil) (l2:=nil) (l3:=nil)(t2:=y);try constructor;tauto. Qed.

(** Aeq is equivalence relation **)
Add Relation tm aeq reflexivity proved by aeq_refl symmetry proved by aeq_sym 
        transitivity proved by aeq_trans as aeq_equivalence.

Lemma irrelevant_binder_aeq: forall l bd M N,
  (forall s, In s (binder_l bd) -> ~ In s (tm_var M ++ tm_var N)) ->
  (forall s, In s (binder_r bd) -> ~ In s (tm_var M ++ tm_var N)) ->
  alpha_eq l M N ->
  alpha_eq (l++bd) M N.
Proof.
  intros. induction H1.
  + constructor.
  + apply str_aeq1. easy. rewrite in_app_iff. now left.
  + apply str_aeq2. 
      - rewrite binder_l_app. apply not_in_app. split. tauto.
        rewrite not_in_Forall. rewrite Forall_forall. intros. specialize H with x.
        apply H in H3. rewrite var_occur_not_eq_dec. solve_notin. 
      - rewrite binder_r_app. apply not_in_app. split. tauto.
        rewrite not_in_Forall. rewrite Forall_forall. intros. specialize H0 with x.
        apply H0 in H3. rewrite var_occur_not_eq_dec. solve_notin. 
  + constructor.
      - apply IHalpha_eq1. intros. specialize H with s. apply H in H1.
        solve_notin. intros. apply H0 in H1. solve_notin.  
      - apply IHalpha_eq2. intros. specialize H with s. apply H in H1.
        solve_notin. intros. apply H0 in H1. solve_notin.  
  + constructor. easy. rewrite update_app. assert(update x x' bd = bd).
    { clear IHalpha_eq H1. 
    induction bd. 
    - reflexivity.
    - destruct a as [[s1 s2] b]. simpl.
      assert (var_occur x s1 = 0).
      { rewrite var_occur_not_eq_dec. specialize H with s1.
      simpl in H. assert (s1 = s1 \/ In s1 (binder_l bd)).
      now left. apply H in H1. tauto. }
      assert (var_occur x' s2 = 0).
      { rewrite var_occur_not_eq_dec. specialize H0 with s2.
      simpl in H0. assert (s2 = s2 \/ In s2 (binder_r bd)).
      now left. apply H0 in H3. des_notin H3. solve_notin. }
      rewrite H1. rewrite H3. simpl. rewrite IHbd. easy. 
      intros. apply H. simpl. tauto. intros. apply H0. simpl. tauto. }
      rewrite H3. apply IHalpha_eq. 
      intros. apply H in H4. solve_notin.
      intros. apply H0 in H4. solve_notin. 
Qed. 


(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(* Critical lemma that relates aeq and substitution    *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

(** Modify the binder list according to renaming list **)
Fixpoint modify(bd:binder_list)(u' v':list (option V)):binder_list:=
match bd,u',v' with
| (u,v,b)::bd0, (Some s1)::u0, (Some s2)::v0 => (s1,s2,b)::(modify bd0 u0 v0)
| (u,v,b)::bd0, None::u0, (Some s)::v0 => (u,s,b)::(modify bd0 u0 v0)
| (u,v,b)::bd0, (Some s)::u0, None::v0 => (s,v,b)::(modify bd0 u0 v0)
| (u,v,b)::bd0, None::u0, None::v0 => (u,v,b)::(modify bd0 u0 v0)
| _ ,_,_ => nil
end.

(** Compute the binders' liveness so that the binder_list is valid **)
Fixpoint compute_valid(bd:binder_list):binder_list:=
match bd with
 | nil => nil
 | (u,v,b)::bd0 => (u,v,true)::(update u v (compute_valid bd0))
end.

(** Compute the current renaming subst_task (each var is renamed with the newest introduced var) **)
Fixpoint renaming_task(u:list V)(u':list (option V)): subst_task:=
match u,u' with
 | nil, nil => nil
 | x::xs, None::us0 =>  let st:= renaming_task xs us0 in reduce x st
 | x::xs, (Some s)::us0 => let st:= renaming_task xs us0 in
                            (x,var s)::(reduce x st)
 | _ , _ => nil
end.
            
Lemma var_equal_compute_valid: forall bd1 bd2,
  binder_var_equal bd1 bd2 ->
  compute_valid bd1 =  compute_valid bd2.
Proof. intros. induction H.  reflexivity. simpl. congruence. Qed.

Lemma renaming_task_sub_is_var: forall s u v,
  is_var (var_sub s (renaming_task u v)).
Proof.
  intros s u. induction u;intros; simpl;destruct v; try constructor.
  destruct o. destruct_eq_dec. 
  constructor. specialize IHu with v. 
  pose proof var_sub_with_task_reduce_other s a (renaming_task u v).
  simpl in H. rewrite <- H;tauto. destruct (var_eq_dec s a).
  subst a. rewrite str_not_in_domain_then_var_sub_is_self. constructor. apply not_in_domain_reduce_self.
  pose proof var_sub_with_task_reduce_other s a (renaming_task u v).
  simpl in H. rewrite <- H;try tauto. specialize IHu with v. tauto.
Qed.

Lemma st_is_var_sub_is_var: forall s st,
  Forall is_var (range st) ->
  is_var (var_sub s st).
Proof.
  intros. induction st.
  + constructor.
  + destruct a. simpl.  apply Forall_cons_iff in H. destruct_eq_dec.
Qed.     

Lemma is_var_reduce: forall x st,
  Forall is_var (range st) ->
  Forall is_var (range (reduce x st)).
Proof.
  intros. induction st.
  + constructor.
  + destruct a. simpl in H. apply Forall_cons_iff in H.
      destruct_eq_dec.  simpl. apply Forall_cons_iff. tauto.
Qed. 

Lemma in_renaming_task_domain_then_in_binder_path: forall x l u,
  In x (domain (renaming_task l u)) ->
  In x l.
Proof.
  intros x l. induction l;intros; simpl in H;destruct u; try inversion H.
  destruct o.
  + simpl in H. destruct H. left. congruence.
      specialize IHl with u. right. apply IHl.
      now apply in_reduce_domain in H.
  + apply in_reduce_domain in H. right. specialize IHl with u. tauto.
Qed.
  
Lemma modify_var_equal: forall bd1 bd2 u v,
  binder_var_equal bd1 bd2 ->
  binder_var_equal (modify bd1 u v) (modify bd2 u v).
Proof.
  intros. revert u v. induction H;intros; simpl.
  + constructor.
  + destruct u; destruct v; try constructor; destruct o;try constructor; destruct o0;try constructor;apply IHbinder_var_equal.
Qed.     

Definition same_var_type (bd:binder_pair):Prop:=
 varsort (fst (fst bd)) = varsort (snd (fst bd)).

Lemma compute_valid_valid: forall bd,
  Forall same_var_type bd ->
  valid_binder (compute_valid bd).
Proof.
  intros. induction bd.
  + constructor.
  + destruct a as [[x y] b]. simpl.  rewrite Forall_forall in H. constructor.
      specialize H with (x,y,b). simpl in H. tauto. apply IHbd. apply Forall_forall.
      intros. apply H. now right.
Qed.

Lemma same_var_type_var_equal: forall bd1 bd2,
  binder_var_equal bd1 bd2 ->
  Forall same_var_type bd1 <->
  Forall same_var_type bd2.
Proof. split;intros;induction H; try easy; apply Forall_cons_iff in H0;apply Forall_cons;tauto. Qed.


(** If a binder list is valid, the result of compute_valid is itself **)
Lemma valid_binder_iff_compute_valid_is_itself: forall bd,
  valid_binder bd <->
  compute_valid bd = bd /\ Forall same_var_type bd .
Proof.
  split;intros.
  + induction H.
      - split. reflexivity. constructor.
      - simpl. destruct IHvalid_binder. split. assert (compute_valid (update x y l) = compute_valid l).
        apply var_equal_compute_valid. apply binder_var_equal_sym. apply update_var_equal.
        rewrite H3.  now rewrite H1. apply Forall_cons. easy. eapply same_var_type_var_equal.
        apply binder_var_equal_sym. apply update_var_equal. easy. 
  + induction bd. constructor.
      destruct a as [[s1 s2] b]. simpl in H. destruct H. inversion H; subst.
      apply Forall_cons_iff in H0. constructor. easy. now apply compute_valid_valid. 
Qed.

Corollary valid_binder_same_var_type: forall bd,
  valid_binder bd -> Forall same_var_type bd.
Proof. intros. now apply valid_binder_iff_compute_valid_is_itself in H. Qed.

Fixpoint list_update (bd1 bd2: binder_list): binder_list:=
  match bd1 with
  | nil => bd2
  | (x,y,b) :: bd0 => update x y (list_update bd0 bd2)
  end.

Lemma list_update_binder_l: forall l st,
  binder_l st = (binder_l (list_update l st)).
Proof.
  intros. induction l.
  + reflexivity.
  + destruct a. destruct p. simpl. now shorten_update. 
Qed.

Lemma list_update_binder_r: forall l st,
  binder_r st = (binder_r (list_update l st)).
Proof.
  intros. induction l.
  + reflexivity.
  + destruct a. destruct p. simpl. now shorten_update. 
Qed.

Lemma list_update_var_equal: forall bd1 bd2 bd,
  binder_var_equal bd1 bd2 ->
  list_update bd1 bd =  list_update bd2 bd.
Proof. intros. induction H. reflexivity. simpl. now rewrite IHbinder_var_equal. Qed.

Lemma true_binder_in_list_updated_list:forall x y l st,
  In (x,y,true)(list_update l st) -> In (x,y,true) st /\ ~ In x (binder_l l) /\ ~ In y (binder_r l).
Proof.
  intros. induction l.
  + tauto.
  + simpl in H. destruct a as [[a1 a2] b].
      apply true_binder_in_updated_list  in H. 
      split;[tauto|split;simpl;apply not_in_cons;tauto].
Qed.
  
Lemma compute_valid_app: forall bd1 bd2,
  compute_valid bd1 ++ list_update bd1 (compute_valid bd2) = compute_valid (bd1 ++ bd2).
Proof.
  intros. induction bd1.
  + reflexivity.
  + destruct a as [[s1 s2] b]. simpl. rewrite <- update_app. now rewrite IHbd1. 
Qed.
    
Lemma compute_valid_length: forall bd,
  length (compute_valid bd) = length bd.
Proof.
  intros. induction bd.
  + reflexivity.
  + destruct a as [[s1 s2] b]. simpl. shorten_update. congruence.
Qed.

(** Old binders can not affect new ones **)
Lemma valid_binder_app: forall bd1 bd2,
  valid_binder (bd1 ++ bd2) ->
  valid_binder bd1.
Proof.
  intros. rewrite valid_binder_iff_compute_valid_is_itself. rewrite valid_binder_iff_compute_valid_is_itself in H.
  destruct H. split.
  pose proof compute_valid_app bd1 bd2. rewrite H in H1.
  pose proof compute_valid_length bd1.
  apply app_injection_length_l in H1; tauto. now apply Forall_app in H0.
Qed.

Lemma compute_valid_after_modify_after_update: forall x y l u v,
  compute_valid (modify (update x y l) u v) = compute_valid (modify l u v).
Proof.
  intros. apply var_equal_compute_valid. apply modify_var_equal.
  apply binder_var_equal_sym. apply update_var_equal.
Qed.

Lemma aeq_refl_free_occur_varong: forall l l' t,
  Forall same_binder l ->
  Forall (fun x => free_occur x t = 0 \/ In (x,x,true) l) (binder_l l') ->
  Forall (fun x => free_occur x t = 0 \/ In (x,x,true) l) (binder_r l') ->
  valid_binder (l++l') ->
  alpha_eq (l++l') t t.
Proof.
  intros. apply valid_binder_app in H2. revert l l' H H0 H1 H2.
  induction t; intros.
  + constructor.
  + induction H2. 
      - simpl. apply str_aeq2; rewrite not_in_Forall; 
        try tauto; rewrite Forall_forall; intros; rewrite Forall_forall in H0; rewrite Forall_forall in H1;
        specialize H0 with x; [apply H0 in H2|apply H1 in H2]; simpl in H2; rewrite var_occur_not_eq_dec in H2;
        rewrite var_occur_not_eq_dec;destruct H2; try tauto;congruence. 
      - rewrite <- Forall_cons_iff in H. destruct H.
        inversion H; subst. rewrite <- update_same_binder in H4.
        destruct (var_eq_dec y s). apply str_aeq1. easy. left. congruence.
        apply IHvalid_binder in H4.
        2:{ rewrite Forall_forall. intros. rewrite Forall_forall in H0. specialize H0 with x.
             apply H0 in H5. destruct H5. tauto. 
             inversion H5;subst. inversion H6; subst. left. 
             simpl. rewrite var_occur_not_eq_dec. easy.
             right. now apply true_binder_in_updated_list in H6. }
        2:{ rewrite Forall_forall. intros. rewrite Forall_forall in H1. specialize H1 with x.
             apply H1 in H5. destruct H5. tauto. 
             inversion H5;subst. inversion H6; subst. left. 
             simpl. rewrite var_occur_not_eq_dec. tauto.
             right. now apply true_binder_in_updated_list in H6. }
       clear IHvalid_binder. inversion H4; subst.
       * apply str_aeq1. easy. right. rewrite in_app_iff.
          rewrite in_app_iff in H9. destruct H9. left. apply irrelevant_update. 
          split; congruence. easy. tauto.
       * apply str_aeq2; simpl; apply deMorgan2;[split;[congruence|]|].
          ++ rewrite binder_l_app. shorten_update. rewrite <- binder_l_app. tauto.      
          ++ rewrite binder_r_app. shorten_update. rewrite <- binder_r_app. tauto.
   + constructor. 
       - apply IHt1; try tauto; rewrite Forall_forall; intros.
          * rewrite Forall_forall in H0. specialize H0 with x. apply H0 in H3.
             destruct H3. left.  zero_r H3. tauto. 
          * rewrite Forall_forall in H1. specialize H1 with x. apply H1 in H3.
             destruct H3. left.  zero_r H3. tauto. 
       - apply IHt2; try tauto; rewrite Forall_forall; intros.
          * rewrite Forall_forall in H0. specialize H0 with x. apply H0 in H3.
             destruct H3. left. zero_r H3. tauto.
          * rewrite Forall_forall in H1. specialize H1 with x. apply H1 in H3.
             destruct H3. left. zero_r H3. tauto.  
   + constructor. easy. rewrite update_app. specialize IHt with ((v, v, true) :: update v v l) (update v v l'). 
       apply IHt. 
       - apply Forall_cons. constructor. apply update_same_binder. tauto.
       - rewrite Forall_forall; intros. rewrite Forall_forall in H0.
         shorten_update. specialize H0 with x.
         apply H0 in H3. simpl in H3. destruct_eq_dec.
         destruct H3. tauto. right. right. apply irrelevant_update. split; congruence. tauto.
       - rewrite Forall_forall; intros. rewrite Forall_forall in H1.
         shorten_update. specialize H1 with x.
         apply H1 in H3. simpl in H3. destruct_eq_dec.
         destruct H3. tauto. right. right. apply irrelevant_update. split; congruence. tauto.
       - now constructor.   
Qed.

(** A stronger lemma about alpha reflexivity **)
Corollary aeq_refl_free_occur: forall l t,
  Forall (fun x => free_occur x t = 0) (binder_l l) ->
  Forall (fun x => free_occur x t = 0) (binder_r l) ->
  valid_binder l ->
  alpha_eq l t t.
Proof.
  intros. pose proof aeq_refl_free_occur_varong nil l t.
  simpl in H2. apply H2.
  + constructor.
  + rewrite Forall_forall. intros. left. rewrite Forall_forall in H. specialize H with x; tauto.
  + rewrite Forall_forall. intros. left. rewrite Forall_forall in H0. specialize H0 with x; tauto.
  + tauto.
Qed.


(** Start proving the critical lemma **)
Lemma modify_update_simpl1: forall x x' bd u v,
  compute_valid (modify ((x, x', true) :: update x x' bd) (None :: u) (None :: v))  =
  (x, x', true) :: update x x' (compute_valid (modify bd u v)).
Proof. intros. simpl. now rewrite compute_valid_after_modify_after_update. Qed.
 
Lemma modify_update_simpl2: forall x x' z bd u' v',
  compute_valid (modify ((x, x', true) :: update x x' bd) (None :: u') (Some z :: v')) =
  (x, z, true) :: update x z (compute_valid (modify bd u' v')).
Proof. intros. simpl. now rewrite compute_valid_after_modify_after_update. Qed.

Lemma modify_update_simpl3: forall x x' z bd u' v',
  compute_valid (modify ((x, x', true) :: update x x' bd) (Some z :: u') (None :: v')) =
  (z, x', true) :: update z x' (compute_valid (modify bd u' v')).
Proof.  intros. simpl. now rewrite compute_valid_after_modify_after_update. Qed.

Lemma modify_update_simpl4: forall x x' z1 z2 bd u' v',
  compute_valid (modify ((x, x', true) :: update x x' bd) (Some z1 :: u') (Some z2 :: v')) =
  (z1, z2, true) :: update z1 z2 (compute_valid (modify bd u' v')).
Proof. intros. simpl. now rewrite compute_valid_after_modify_after_update. Qed.

(** Introduced var can not be current living renaming vars , it should also have the same type**)
Inductive good_new_var: list V -> list (option V) -> Prop:=
| good_new_var_nil: good_new_var nil nil
| good_new_var_none: forall x xs us,
    good_new_var xs us ->
    st_tm_occur x (reduce x (renaming_task xs us)) = 0->
    good_new_var (x::xs) (None::us)
| good_new_var_some: forall x xs u us,
    varsort x = varsort u ->
    good_new_var xs us ->
    st_tm_occur u (reduce x (renaming_task xs us)) = 0 ->
    good_new_var (x::xs) (Some u::us)
.

(** Introduced var can not be in the currently living subst_task **)
Inductive st_new_var: subst_task -> list V -> list (option V) -> Prop:=
| st_new_var_nil: forall st, st_new_var st nil nil
| st_new_var_none: forall st x xs us,
    st_new_var st xs us ->
    st_tm_occur x (list_reduce (x::xs) st) = 0 ->
    st_new_var st (x::xs) (None::us)
| st_new_var_some: forall st x xs u us,
    st_new_var st xs us ->
    st_tm_occur u (list_reduce (x::xs) st) = 0->
    st_new_var st (x::xs) (Some u::us)
.

(** Compute the vars that can not be free in the current term **)
Inductive tm_new_var: list V -> list (option V) -> V -> Prop:=
| tm_new_var_cons1: forall x y l l',
   tm_new_var (x::l) (Some y:: l') y
| tm_new_var_cons2: forall x y oy l l',
  tm_new_var l l' y ->
  x <> y ->
  tm_new_var (x::l) (oy::l') y
.


(** The conditions of the critical lemma **)
Record aeq_sub_Assumption (M N:tm)(st:subst_task) (bd:binder_list) (u' v':list (option V)):={
  binder_valid: valid_binder bd;
  length_binder_r: length v' = length bd;
  length_binder_l: length u' = length bd;
  tm_new_var_u: forall x, tm_new_var (binder_l bd) u' x -> free_occur x M =0;
  tm_new_var_v: forall x, tm_new_var (binder_r bd) v' x -> free_occur x N =0;
  good_new_var_u: good_new_var (binder_l bd) u';
  good_new_var_v: good_new_var (binder_r bd) v';
  st_new_var_u: st_new_var st (binder_l bd) u';
  st_new_var_v: st_new_var st (binder_r bd) v'
}.

Lemma subst_renaming_task_l: forall x z bd u st t,
 (subst (list_reduce (x :: binder_l bd) st ++ renaming_task (x :: binder_l bd) (Some z :: u)) t) =
  (subst  ((x, var z) :: list_reduce (x :: binder_l bd) st ++ reduce x (renaming_task (binder_l bd) u))
     t).
Proof. intros. apply subst_reduce_swap. Qed.

Lemma renaming_task_sub_same_var_type: forall s v xs us,
  good_new_var xs us ->
  var s = var_sub v (renaming_task xs us) ->
  varsort s = varsort v.
Proof.
  intros. revert us H H0. induction xs; intros.
  + inversion H; subst. simpl in H0. injection H0 as H0.  subst v. easy.
  + inversion H; subst.
      - simpl in H0. destruct (var_eq_dec v a). subst a. 
        rewrite var_sub_with_task_reduce_self in H0. congruence.
        rewrite <- var_sub_with_task_reduce_other in H0. eauto. easy.
      - simpl in H0. destruct (var_eq_dec v a).
         * congruence.
         *  rewrite <- var_sub_with_task_reduce_other in H0. eauto. easy.
Qed.


Lemma modify_same_var_type: forall bd us vs,
 Forall same_var_type bd ->
 good_new_var (binder_l bd) us ->
 good_new_var (binder_r bd) vs ->
 Forall same_var_type (modify bd us vs). 
Proof.
  induction bd; intros.
  + constructor.
  + destruct a as [[x y] b]. simpl in H0. simpl in H1. inversion H0; inversion H1; subst; simpl;
      apply Forall_cons_iff in H; destruct H; apply Forall_cons; try now apply IHbd. 
     - easy.  
     - cbv in H. cbv. congruence. 
     - cbv in H. cbv. congruence. 
     - cbv in H. cbv. congruence.
Qed.
     
Lemma subst_renaming_task_r: forall x z bd u st t, 
 (subst (list_reduce (x :: binder_r bd) st ++ renaming_task (x :: binder_r bd) (Some z :: u)) t) =
  (subst  ((x, var z) :: list_reduce (x :: binder_r bd) st ++ reduce x (renaming_task (binder_r bd) u))
     t).
Proof. intros. apply subst_reduce_swap. Qed. 

Lemma critical_var1_1: forall (s s1 s3: V)  x l u',
 ( forall x0 : V, tm_new_var (x ::  l) (Some s3 :: u') x0 -> var_occur x0 s1 = 0) ->
  s1 <> x ->
  var s = var_sub s1 (reduce x (renaming_task l u'))->
  st_tm_occur s3 (reduce x (renaming_task l u')) = 0 ->
  s <> s3.
Proof.
  intros. assert (s1<>s3).
  specialize H with s3. assert (tm_new_var (x :: l) (Some s3 :: u') s3) by constructor.
  apply H in H3. rewrite var_occur_not_eq_dec in H3. congruence.
  pose proof var_sub_range s1 (reduce x (renaming_task l u')).
  destruct H4.
  + pose proof var_sub_keep_no_occur s1 s3 (reduce x (renaming_task l u')).
      simpl in  H5. rewrite <- H1 in H5. simpl in H5. rewrite var_occur_not_eq_dec in H5. 
      assert (s3<>s). apply H5;[congruence| tauto]. congruence.
  + congruence. 
Qed.

Lemma critical_var1_2: forall (s0 s2 y:V) l v',
   s2 <> y ->
   var s0 = var_sub s2 (reduce y (renaming_task  l v')) ->
   st_tm_occur y (reduce y (renaming_task  l v')) = 0 ->
   y <> s0.
Proof.
  intros. pose proof var_sub_range s2 (reduce y (renaming_task  l v')).
  destruct H2.
  + pose proof var_sub_keep_no_occur s2 y  (reduce y (renaming_task l v')).
      simpl in H3. rewrite <- H0 in H3. simpl in H3. rewrite  var_occur_not_eq_dec  in H3.
      apply H3;[congruence|tauto].
  + congruence. 
Qed.

Lemma critical_var1: forall (s1 s2: V) st bd u' v',
  In (s1,s2,true) bd -> 
  aeq_sub_Assumption s1 s2 st bd u' v' ->
  alpha_eq (compute_valid (modify bd u' v')) (var_sub s1 (renaming_task (binder_l bd) u'))
  (var_sub s2 (renaming_task (binder_r bd) v')).
Proof.
  intros. destruct H0. clear st st_new_var_u0 st_new_var_v0.
  pose proof renaming_task_sub_is_var s1 (binder_l bd) u'.
  pose proof renaming_task_sub_is_var s2 (binder_r bd) v'.
  inversion H0. inversion H1. clear H0 H1. apply str_aeq1.
 { apply renaming_task_sub_same_var_type in H3. apply renaming_task_sub_same_var_type in H4. 
  apply valid_binder_same_var_type in binder_valid0. rewrite Forall_forall in binder_valid0.
  apply binder_valid0 in H. cbv in H. congruence. easy. easy. }
  revert u' v' s s0 length_binder_l0 length_binder_r0 good_new_var_u0 good_new_var_v0 H3 H4 tm_new_var_v0 tm_new_var_u0.
  induction binder_valid0;intros.
  + inversion H.
  + destruct u';destruct v';try inversion length_binder_l0;try inversion length_binder_r0;subst.
      clear length_binder_l0. clear length_binder_r0.
      destruct o;destruct o0;simpl in H3;simpl in H4;simpl in good_new_var_u0;simpl in good_new_var_v0; 
     simpl in tm_new_var_u0;simpl in tm_new_var_v0; shorten_update.
     - destruct (var_eq_dec s1 x); destruct (var_eq_dec s2 y); subst. 
       *  apply tm_var_eq in H3. apply tm_var_eq in H4. subst. now left.
       *  assert (In (x, y, true) ((x, y, true) :: update x y l)) by now left.
          pose proof valid_binder_injective_l x y s2 ((x, y, true) :: update x y l).
          apply H6 in H1. congruence. now constructor. easy.
       *  assert (In (x, y, true) ((x, y, true) :: update x y l)) by now left.
          pose proof valid_binder_injective_r x y s1 ((x, y, true) :: update x y l).
          apply H6 in H1. congruence. now constructor. easy.
       *  right. rewrite compute_valid_after_modify_after_update. 
           inversion good_new_var_u0;subst. inversion good_new_var_v0;subst.
           assert (s<>v). pose proof critical_var1_1 s s1 v x (binder_l l) u'. now apply H1.  
           assert(s0<>v0). pose proof critical_var1_1 s0 s2 v0 y (binder_r l) v'. now apply H6.       
           apply irrelevant_update. easy. 
           apply IHbinder_valid0;try tauto; clear IHbinder_valid0. 
           destruct H. congruence. now apply true_binder_in_updated_list in H.  
           now rewrite <-  var_sub_with_task_reduce_other in H3.
           now rewrite <-  var_sub_with_task_reduce_other in H4.
           intros.  destruct (var_eq_dec y x0).
           simpl. rewrite  var_occur_not_eq_dec. congruence.
           apply tm_new_var_v0. apply tm_new_var_cons2;tauto.
           intros. destruct (var_eq_dec x x0).
           simpl. rewrite  var_occur_not_eq_dec. congruence.
           apply tm_new_var_u0. apply tm_new_var_cons2; tauto.
      -   destruct (var_eq_dec s1 x);subst.
           * pose proof valid_binder_injective_l x y s2 ((x, y, true) :: update x y l).
              assert (y=s2). apply H1. now constructor. now left. easy.
              left. subst s2. rewrite var_sub_with_task_reduce_self in H4. congruence.
           * right.  rewrite compute_valid_after_modify_after_update. 
              inversion good_new_var_u0; subst. inversion good_new_var_v0;subst.
              destruct (var_eq_dec y s2). rewrite e in H. 
              assert (In (x, s2, true) ((x, s2, true) :: update x s2 l)) by now left.
              pose proof valid_binder_injective_r s1 s2 x ((x, s2, true) :: update x s2 l).
              assert (s1=x). apply H6. constructor. congruence. easy. easy. easy. congruence.
              assert (s<>v). pose proof critical_var1_1 s s1 v x (binder_l l) u'. now apply H1.
              assert (y<>s0). pose proof critical_var1_2 s0 s2 y (binder_r l) v'. apply H6; try tauto;congruence.
              apply irrelevant_update. split;congruence.
              apply IHbinder_valid0;try tauto; clear IHbinder_valid0. 
              destruct H. congruence. now apply true_binder_in_updated_list in H.  
              now rewrite <- var_sub_with_task_reduce_other in H3. 
              rewrite <- var_sub_with_task_reduce_other in H4; try tauto; congruence.
              intros. simpl. destruct (var_eq_dec y x0).  rewrite  var_occur_not_eq_dec. congruence.
              apply tm_new_var_v0. now constructor. 
              intros. simpl. destruct (var_eq_dec x x0).  rewrite var_occur_not_eq_dec. congruence.
              apply tm_new_var_u0. now apply tm_new_var_cons2. 
      -  destruct (var_eq_dec s2 y);subst.
          * left. assert (s1=x). pose proof valid_binder_injective_r s1 y x ((x, y, true) :: update x y l).
             apply H1. now constructor.  tauto. now left. subst s1. rewrite var_sub_with_task_reduce_self in H3. congruence. 
          * right. destruct (var_eq_dec s1 x). subst. 
             pose proof valid_binder_injective_l x s2 y ((x, y, true) :: update x y l). assert (s2=y). apply H1.
             now constructor. easy. now left. contradiction.  
             inversion good_new_var_u0; subst. inversion good_new_var_v0;subst.
             rewrite compute_valid_after_modify_after_update. 
             assert (s<>x). pose proof critical_var1_2 s s1 x (binder_l l) u'. assert (x<>s) by tauto. congruence.
             assert (s0<>v). pose proof critical_var1_1 s0 s2 v y (binder_r l) v'. now apply H6.
             apply irrelevant_update. split;congruence.
             apply IHbinder_valid0;try tauto; clear IHbinder_valid0.
             destruct H. congruence. now apply true_binder_in_updated_list in H. 
             now rewrite <- var_sub_with_task_reduce_other in H3.
             now rewrite <- var_sub_with_task_reduce_other in H4.
             intros. simpl. destruct (var_eq_dec x0 y). rewrite var_occur_not_eq_dec. congruence.
             apply tm_new_var_v0. apply tm_new_var_cons2;try tauto; congruence.
             intros. simpl. destruct (var_eq_dec x0 x).  rewrite var_occur_not_eq_dec. congruence.
             apply tm_new_var_u0. constructor;try tauto; congruence.
      -  destruct (var_eq_dec s1 x); destruct (var_eq_dec s2 y); subst.
          * rewrite var_sub_with_task_reduce_self in H3. rewrite var_sub_with_task_reduce_self in H4.
             left. congruence.
          * pose proof valid_binder_injective_l x s2 y ((x, y, true) :: update x y l).
             assert (s2=y). apply H1. now constructor. easy. now left. congruence.
          * pose proof valid_binder_injective_r s1 y x ((x, y, true) :: update x y l).
             assert (s1=x). apply H1. now constructor. easy. now left. congruence.
          * right. inversion good_new_var_u0;inversion good_new_var_v0;subst. 
             rewrite compute_valid_after_modify_after_update.
             assert (x<>s). pose proof critical_var1_2 s s1 x (binder_l l) u'. now apply H1. 
             assert (y<>s0).  pose proof critical_var1_2 s0 s2 y (binder_r l) v'. now apply H6. 
             apply irrelevant_update. split;congruence.
             apply IHbinder_valid0;try tauto; clear IHbinder_valid0.
             destruct H. congruence. apply true_binder_in_updated_list in H. tauto.
             rewrite <- var_sub_with_task_reduce_other in H3;tauto.
             rewrite <- var_sub_with_task_reduce_other in H4;tauto.
             intros. simpl. destruct (var_eq_dec x0 y). rewrite var_occur_not_eq_dec. congruence.
             apply tm_new_var_v0. constructor.  tauto. congruence.
             intros. simpl. destruct (var_eq_dec x0 x).  rewrite var_occur_not_eq_dec. congruence.
             apply tm_new_var_u0. constructor.  tauto. congruence.
Qed.
  
  
Local Ltac IHalpha_eq_simpl x x' bd IHalpha_eq:=
 assert ((binder_l ((x, x', true) :: update x x' bd))= x::(binder_l bd)) as H'; 
 [simpl; rewrite <- update_binder_l; reflexivity |];  
 assert ((binder_r ((x, x', true) :: update x x' bd))= x'::(binder_r bd)) as H'';
 [simpl; rewrite <- update_binder_r; reflexivity |];
 repeat rewrite H' in IHalpha_eq; repeat rewrite H'' in IHalpha_eq;
 clear H' H'';
 repeat rewrite reduce_app;
 repeat rewrite list_reduce_cons.


Lemma critical_var2_1: forall (s:V) bd st u' v',
  ~ In s (binder_l bd) ->
  aeq_sub_Assumption s s st bd u' v' ->
  Forall (fun x => free_occur x (subst (list_reduce (binder_l bd) st) s) = 0) (binder_l (compute_valid (modify bd u' v'))).
Proof.
  intros. destruct H0.
  clear good_new_var_u0 good_new_var_v0 st_new_var_v0 tm_new_var_v0. 
  revert u' v' length_binder_l0 length_binder_r0 tm_new_var_u0  st_new_var_u0.
  induction binder_valid0; intros; rewrite Forall_forall; intros.  
  + inversion H0.
  + destruct u'. inversion length_binder_l0. simpl in st_new_var_u0. 
      destruct v'. inversion length_binder_r0. 
      simpl in tm_new_var_u0.  simpl.  shorten_update.
      destruct o; destruct o0; specialize IHbinder_valid0 with u' v'; rewrite Forall_forall in IHbinder_valid0;
      inversion st_new_var_u0; subst; simpl in H1.
      - destruct H1.
        * subst. rewrite list_reduce_cons. assert (x0<>s).
           specialize tm_new_var_u0 with x0. rewrite <- var_occur_not_eq_dec.
           apply tm_new_var_u0. constructor.
           now apply var_sub_keep_no_occur. 
        * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_l in H1.
           des_notin H. shorten_update. rewrite <- var_sub_with_task_reduce_other; try congruence.
           apply IHbinder_valid0;try tauto. 
           inversion length_binder_l0;subst. now shorten_update. 
           inversion length_binder_r0;subst. now shorten_update. 
           intros. simpl. destruct (var_eq_dec x1 x). rewrite var_occur_not_eq_dec. congruence.
           apply tm_new_var_u0. constructor.  tauto. congruence.
      - destruct H1.
        * subst. rewrite list_reduce_cons. assert (x0<>s). 
           specialize tm_new_var_u0 with x0. rewrite <- var_occur_not_eq_dec.
           apply tm_new_var_u0. constructor.  now apply var_sub_keep_no_occur.
        * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_l in H1. 
           des_notin H. shorten_update.  rewrite <- var_sub_with_task_reduce_other; try congruence.
           apply IHbinder_valid0;try tauto. 
           inversion length_binder_l0;subst. now shorten_update.
           inversion length_binder_r0;subst. now shorten_update.
           intros. simpl. destruct (var_eq_dec x1 x). rewrite var_occur_not_eq_dec. congruence.
           apply tm_new_var_u0. constructor.  tauto. congruence.
      - destruct H1.
        * subst. rewrite list_reduce_cons. des_notin H. shorten_update. apply var_sub_keep_no_occur;tauto.
        * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_l in H1.
           des_notin H. shorten_update. rewrite <- var_sub_with_task_reduce_other; try congruence.
           apply IHbinder_valid0;try tauto. 
           inversion length_binder_l0;subst. shorten_update. tauto.
           inversion length_binder_r0;subst. shorten_update. tauto.
           intros. simpl. destruct (var_eq_dec x1 x). rewrite var_occur_not_eq_dec. congruence.
           apply tm_new_var_u0. constructor.  tauto. congruence.
      - destruct H1.
        * subst. rewrite list_reduce_cons. des_notin H. shorten_update.  apply var_sub_keep_no_occur;tauto.
        * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_l in H1.
           des_notin H.  shorten_update. rewrite <- var_sub_with_task_reduce_other; try congruence.
           apply IHbinder_valid0;try tauto. 
           inversion length_binder_l0;subst. now shorten_update.
           inversion length_binder_r0;subst. now shorten_update. 
           intros. simpl. destruct (var_eq_dec x1 x). rewrite var_occur_not_eq_dec. congruence.
           apply tm_new_var_u0. constructor. easy. congruence. 
Qed.

Lemma critical_var2_2: forall (s:V) bd st u' v',
  ~ In s (binder_r bd) ->
  aeq_sub_Assumption s s st bd u' v' ->
  Forall (fun x => free_occur x (subst (list_reduce (binder_r bd) st) s) = 0) (binder_r (compute_valid (modify bd u' v'))).
Proof.
  intros. destruct H0.
  clear good_new_var_u0 good_new_var_v0 st_new_var_u0 tm_new_var_u0. 
  revert u' v' length_binder_l0 length_binder_r0 tm_new_var_v0  st_new_var_v0.
  induction binder_valid0; intros; rewrite Forall_forall; intros.  
  + inversion H0.
  + destruct u'. inversion length_binder_l0. simpl in st_new_var_v0. 
      destruct v'. inversion length_binder_r0. 
      simpl in tm_new_var_v0.  simpl.  shorten_update.
      destruct o; destruct o0; specialize IHbinder_valid0 with u' v'; rewrite Forall_forall in IHbinder_valid0;
        inversion st_new_var_v0; subst; simpl in H1.
      - destruct H1. 
        * subst. rewrite list_reduce_cons. assert (x0<>s).
           specialize tm_new_var_v0 with x0. rewrite <- var_occur_not_eq_dec.
           apply tm_new_var_v0. constructor.
           now apply var_sub_keep_no_occur.
        * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_r in H1.
           des_notin H. shorten_update. rewrite <- var_sub_with_task_reduce_other; try congruence.
           apply IHbinder_valid0;try tauto. 
           inversion length_binder_l0;subst. shorten_update. tauto.
           inversion length_binder_r0;subst. shorten_update. tauto.
           intros. simpl. destruct (var_eq_dec x1 y). rewrite var_occur_not_eq_dec. congruence.
           apply tm_new_var_v0. constructor.  tauto. congruence.
      -  destruct H1.
        * subst. rewrite list_reduce_cons. des_notin H.  shorten_update. now apply var_sub_keep_no_occur.
        * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_r in H1. 
           des_notin H.  shorten_update. rewrite <- var_sub_with_task_reduce_other; try congruence.
         apply IHbinder_valid0;try tauto. 
         inversion length_binder_l0;subst. now shorten_update.
         inversion length_binder_r0;subst. now shorten_update. 
         intros. simpl. destruct (var_eq_dec x1 y). rewrite var_occur_not_eq_dec. congruence.
         apply tm_new_var_v0. constructor.  tauto. congruence.
      -  destruct H1.
         * subst. rewrite list_reduce_cons. assert (x0<>s).
            specialize tm_new_var_v0 with x0. rewrite <- var_occur_not_eq_dec.
            apply tm_new_var_v0. constructor.
            now apply var_sub_keep_no_occur.
         * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_r in H1.
            des_notin H. shorten_update. rewrite <- var_sub_with_task_reduce_other; try congruence.
            apply IHbinder_valid0;try tauto. 
            inversion length_binder_l0;subst. now shorten_update. 
            inversion length_binder_r0;subst. now shorten_update.
            intros. simpl. destruct (var_eq_dec x1 y). rewrite var_occur_not_eq_dec. congruence.
            apply tm_new_var_v0. constructor.  tauto. congruence.
      - destruct H1.
        * subst. rewrite list_reduce_cons. des_notin H.  shorten_update.  now apply var_sub_keep_no_occur.
        * rewrite compute_valid_after_modify_after_update in H1. rewrite <- update_binder_r in H1.
           des_notin H. shorten_update. rewrite <- var_sub_with_task_reduce_other; try congruence.
           apply IHbinder_valid0;try tauto. 
           inversion length_binder_l0;subst. now shorten_update.
           inversion length_binder_r0;subst. now shorten_update.
           intros. simpl. destruct (var_eq_dec x1 y). rewrite var_occur_not_eq_dec. congruence.
           apply tm_new_var_v0. constructor. easy. congruence. 
Qed.

Lemma aeq_sub_Assumption_app: forall t1 t2 t3 t4 st bd u' v',
  aeq_sub_Assumption (app t1 t2) (app t3 t4) st bd u' v' ->
  aeq_sub_Assumption t1 t3 st bd u' v' /\ aeq_sub_Assumption t2 t4 st bd u' v' .
Proof.
  intros. destruct H. split.
  + split; try tauto; intros.
      - specialize tm_new_var_u0 with x. apply tm_new_var_u0 in H. zero_r H. 
      - specialize tm_new_var_v0 with x. apply tm_new_var_v0 in H.  zero_r H.
  + split; try tauto; intros.
      - specialize tm_new_var_u0 with x. apply tm_new_var_u0 in H. zero_r H.
      - specialize tm_new_var_v0 with x. apply tm_new_var_v0 in H. zero_r H.
Qed.


Lemma aeq_sub_Assumption_none_none: forall x x' t1 t2 st bd u' v',
  varsort x =varsort x' ->
  st_tm_occur x (list_reduce (x :: binder_l bd) st) = 0 ->
  st_tm_occur x' (list_reduce (x' :: binder_r bd) st) = 0 ->
  st_tm_occur x (reduce x (renaming_task (binder_l bd) u')) = 0 ->
  st_tm_occur x' (reduce x' (renaming_task (binder_r bd) v')) = 0 ->
  aeq_sub_Assumption (abs x t1) (abs x' t2) st bd u' v' ->
  aeq_sub_Assumption t1 t2 st ((x, x', true) :: update x x' bd) 
    (None :: u') (None :: v').
Proof.
  intros. destruct H4. split;try tauto; simpl; shorten_update; try congruence; try constructor; try tauto; try solve_notin.
  + intros. specialize tm_new_var_u0 with x0.  
      simpl in H4. destruct (var_eq_dec x0 x).
      subst x0. inversion H4;subst. congruence. 
      shorten_update. inversion H4;subst. apply tm_new_var_u0 in H10. 
      simpl in H10. destruct_eq_dec. 
  + intros. specialize tm_new_var_v0 with x0.  
      simpl in H4. destruct (var_eq_dec x0 x').
      subst x0. inversion H4;subst. congruence. 
      shorten_update. inversion H4;subst. apply tm_new_var_v0 in H10. 
      simpl in H10. destruct_eq_dec.
Qed.

Lemma aeq_sub_Assumption_none_some: forall x x' z t1 t2 st bd u' v',
varsort x = varsort x' ->
z =
       newvar
         (x'
          :: tm_var t2 ++
             task_var
               (reduce x'
                  (list_reduce (binder_r bd) st ++
                   renaming_task (binder_r bd) v'))) (varsort x') ->
st_tm_occur x (list_reduce (x :: binder_l bd) st) = 0 ->
st_tm_occur x (reduce x (renaming_task (binder_l bd) u')) = 0 ->
aeq_sub_Assumption (abs x t1) (abs x' t2) st bd u' v' ->
aeq_sub_Assumption t1 t2 st ((x, x', true) :: update x x' bd) 
  (None :: u') (Some z :: v').
Proof.
  intros. destruct H3. split;try tauto; simpl; shorten_update; try congruence; try constructor; try tauto; try solve_notin.
  + intros. specialize tm_new_var_u0 with x0. 
      destruct (var_eq_dec x0 x). subst x0. inversion H3; subst. congruence.
      inversion H3; subst. apply tm_new_var_u0 in H9. simpl in H9. destruct_eq_dec.
  + intros. specialize tm_new_var_v0 with x0.  
      inversion H3; subst. solve_notin. 
      apply tm_new_var_v0 in H9. simpl in H9. destruct_eq_dec.
  + subst z. now rewrite newvar_sort. 
Qed.


Lemma aeq_sub_Assumption_some_none: forall x x' z t1 t2 st bd u' v',
varsort x = varsort x' ->
z =
       newvar
         (x
          :: tm_var t1 ++
             task_var
               (reduce x
                  (list_reduce (binder_l bd) st ++
                   renaming_task (binder_l bd) u'))) (varsort x) ->
st_tm_occur x' (list_reduce (x' :: binder_r bd) st) = 0 ->
st_tm_occur x' (reduce x' (renaming_task (binder_r bd) v')) = 0 ->
aeq_sub_Assumption (abs x t1) (abs x' t2) st bd u' v' ->
aeq_sub_Assumption t1 t2 st ((x, x', true) :: update x x' bd) 
  (Some z :: u') (None :: v').
Proof.
  intros. destruct H3. split;try tauto; simpl; shorten_update; try congruence; try constructor; try tauto; try solve_notin.
  + intros. specialize tm_new_var_u0 with x0. inversion H3;subst. solve_notin.
      shorten_update. apply tm_new_var_u0 in H9. simpl in H9. destruct_eq_dec.
  + intros. specialize tm_new_var_v0 with x0. inversion H3;subst.
      apply tm_new_var_v0 in H9. simpl in H9. destruct_eq_dec.
  + subst z. now rewrite newvar_sort. 
Qed. 

Lemma aeq_sub_Assumption_some_some: forall x x' z1 z2 t1 t2 st bd u' v',
varsort x = varsort x' ->
z1 =
        newvar
          (x
           :: tm_var t1 ++
              task_var
                (reduce x (list_reduce (binder_l bd) st ++ renaming_task (binder_l bd) u'))) (varsort x) ->
z2 =
        newvar
          (x'
           :: tm_var t2 ++
              task_var
                (reduce x' (list_reduce (binder_r bd) st ++ renaming_task (binder_r bd) v'))) (varsort x') ->
aeq_sub_Assumption (abs x t1) (abs x' t2) st bd u' v' -> 
aeq_sub_Assumption t1 t2 st ((x, x', true) :: update x x' bd) (Some z1 :: u') (Some z2 :: v').  
Proof.
  intros. destruct H2. split;try tauto; simpl; shorten_update; try congruence; try constructor; try tauto; try solve_notin.
  + intros. specialize tm_new_var_u0 with x0. inversion H2;subst. solve_notin.
      shorten_update. apply tm_new_var_u0 in H8. simpl in H8. destruct_eq_dec.
  + intros. specialize tm_new_var_v0 with x0. inversion H2;subst. solve_notin.
      shorten_update. apply tm_new_var_v0 in H8. simpl in H8. destruct_eq_dec.
  + subst z1. now rewrite newvar_sort.
  + subst z2. now rewrite newvar_sort.
Qed.
 

(** The critical, stronger lemma for the substituion theorem **)
Lemma critical: forall M N (st:subst_task) (bd:binder_list)(u' v':list (option V)),
  aeq_sub_Assumption M N st bd u' v'->
  alpha_eq bd M N ->
  alpha_eq (compute_valid (modify bd u' v')) 
  (subst (list_reduce (binder_l bd) st ++ renaming_task (binder_l bd) u') M)
  (subst (list_reduce (binder_r bd) st ++ renaming_task (binder_r bd) v') N).
Proof.
  intros. revert u' v' H. 
  induction H0;intros.
  + constructor.
  + simpl. assert (H2:=H0). apply in_binder_l in H2. assert(H3:=H0). apply in_binder_r in H3.
      pose proof var_sub_with_var_not_in_app_domain_l (list_reduce (binder_l bd) st) (renaming_task (binder_l bd) u') s1.
      simpl in H4. rewrite H4. 2: now apply not_in_domain_list_reduce_containing_self.
      pose proof var_sub_with_var_not_in_app_domain_l (list_reduce (binder_r bd) st ) (renaming_task (binder_r bd) v') s2.
      simpl in H5. rewrite H5. 2: now apply not_in_domain_list_reduce_containing_self. 
      clear H3 H4. pose proof critical_var1 s1 s2 st bd u' v'. now apply H3. 
  + pose proof var_sub_with_var_not_in_app_domain_r (list_reduce (binder_l bd) st ) (renaming_task (binder_l bd) u') s.
      rewrite H2. 2:{ pose proof in_vars_dec s (domain (renaming_task (binder_l bd) u')) as H3.
      destruct H3 as [H3|H3];try tauto. apply in_renaming_task_domain_then_in_binder_path in H3. contradiction. } clear H2. 
      pose proof var_sub_with_var_not_in_app_domain_r (list_reduce (binder_r bd) st ) (renaming_task (binder_r bd) v') s.
      rewrite H2. 2:{ pose proof in_vars_dec s (domain (renaming_task (binder_r bd) v')) as H3.
      destruct H3 as [H3|H3]; try tauto. apply in_renaming_task_domain_then_in_binder_path in H3. contradiction. } clear H2.
      assert(Forall (fun x : V => free_occur x (subst (list_reduce (binder_l bd) st) s) = 0)
       (binder_l (compute_valid (modify bd u' v')))). apply critical_var2_1; tauto.
      assert(Forall (fun x : V => free_occur x (subst (list_reduce (binder_r bd) st) s) = 0)
       (binder_r (compute_valid (modify bd u' v')))). apply critical_var2_2; tauto.
      rewrite <- var_sub_with_task_list_reduce_not_containing_self; try tauto.  rewrite <- var_sub_with_task_list_reduce_not_containing_self; try tauto. 
      rewrite <- var_sub_with_task_list_reduce_not_containing_self in H2; try tauto. rewrite <- var_sub_with_task_list_reduce_not_containing_self in H3; try tauto.
      apply aeq_refl_free_occur; try tauto. apply compute_valid_valid. 
      destruct H1. apply modify_same_var_type; try easy. now apply valid_binder_same_var_type.
  + constructor. 
      - apply IHalpha_eq1. apply aeq_sub_Assumption_app in H; tauto.
      - apply IHalpha_eq2. apply aeq_sub_Assumption_app in H; tauto.
  + simpl. 
      assert(st_tm_occur x (reduce x (list_reduce (binder_l bd) st ++ renaming_task (binder_l bd) u'))= 
      st_tm_occur x (reduce x (list_reduce (binder_l bd) st)) +st_tm_occur x (reduce x (renaming_task (binder_l bd) u'))).
      rewrite reduce_app. rewrite st_tm_occur_app. reflexivity.
      assert(st_tm_occur x' (reduce x' (list_reduce (binder_r bd) st ++ renaming_task (binder_r bd) v'))= 
      st_tm_occur x' (reduce x' (list_reduce (binder_r bd) st)) +st_tm_occur x' (reduce x' (renaming_task (binder_r bd) v'))).
      rewrite reduce_app. rewrite st_tm_occur_app. reflexivity.  
      destruct (st_tm_occur x (reduce x (list_reduce (binder_l bd) st ++ renaming_task (binder_l bd) u')));
      destruct (st_tm_occur x' (reduce x' (list_reduce (binder_r bd) st ++ renaming_task (binder_r bd) v'))).
      - constructor. easy. specialize IHalpha_eq with (None::u') (None::v').
        IHalpha_eq_simpl x x' bd IHalpha_eq. 
        rewrite modify_update_simpl1 in IHalpha_eq. 
        apply IHalpha_eq. apply zero_sum_l in H2. destruct H2. 
        apply zero_sum_l in H3. destruct H3. 
        rewrite list_reduce_cons in H2. rewrite list_reduce_cons in H3.
        apply aeq_sub_Assumption_none_none; tauto.
      - constructor. now rewrite newvar_sort.  remember (newvar
           (x' :: tm_var t2 ++ task_var (reduce x' (list_reduce (binder_r bd) st ++ renaming_task (binder_r bd) v'))) (varsort x')) as z.
        specialize IHalpha_eq with (None::u') (Some z::v').
        IHalpha_eq_simpl x x' bd IHalpha_eq. 
        rewrite modify_update_simpl2 in IHalpha_eq.
        rewrite subst_renaming_task_r in IHalpha_eq. apply IHalpha_eq.
        clear H3. apply zero_sum_l in H2. destruct H2.
        apply aeq_sub_Assumption_none_some; tauto.
      - constructor. now rewrite newvar_sort.  remember (newvar
        (x:: tm_var t1 ++ task_var  (reduce x
         (list_reduce (binder_l bd) st ++ renaming_task (binder_l bd) u'))) (varsort x)) as z.
        specialize IHalpha_eq with (Some z::u') (None::v').
        IHalpha_eq_simpl x x' bd IHalpha_eq. 
        rewrite modify_update_simpl3 in IHalpha_eq. 
        rewrite subst_renaming_task_l in IHalpha_eq. apply IHalpha_eq.
        clear H2. apply zero_sum_l in H3. destruct H3. 
        apply aeq_sub_Assumption_some_none; tauto. 
      - constructor. now repeat rewrite newvar_sort.  remember (newvar
        (x:: tm_var t1 ++task_var (reduce x
               (list_reduce (binder_l bd) st ++ renaming_task (binder_l bd) u'))) (varsort x)) as z1.
        remember (newvar (x' :: tm_var t2 ++ task_var (reduce x'
              (list_reduce (binder_r bd) st ++ renaming_task (binder_r bd) v')))(varsort x')) as z2.
        specialize IHalpha_eq with (Some z1::u') (Some z2::v').
        IHalpha_eq_simpl x x' bd IHalpha_eq. 
        rewrite modify_update_simpl4 in IHalpha_eq.
        rewrite subst_renaming_task_l in IHalpha_eq.
        rewrite subst_renaming_task_r in IHalpha_eq.
        apply IHalpha_eq.
        apply aeq_sub_Assumption_some_some; tauto.
Qed.
  
(** If two terms are alpha-equivalent, substituting them with the same subst_task will preserve the equivalence **)
Theorem subst_same_st_aeq: forall M N st,
  M =a= N ->
  subst st M =a= subst st N.
Proof.
  intros. pose proof critical M N st nil nil nil.
  simpl in H0. repeat rewrite <- app_nil_end in H0.
  apply H0; try tauto.
  split; try constructor;try tauto;try intros; inversion H1.
Qed.

Instance Proper_subst: Proper (eq==> aeq ==> aeq) subst.
Proof.
 intros st1 st2 ? ? ? ?. rewrite H. apply subst_same_st_aeq. tauto.
Qed.
 
(** Renaming a binder is still alpha equivalent **)
Lemma renaming_aeq: forall x s M,
  varsort x = varsort s ->
  free_occur s M = 0->
  abs x M =a= abs s (subst [(x,var s)] M).
Proof.
  intros. constructor. easy. simpl.
  pose proof critical M M nil [(x,x,true)] [None] [(Some s)].
  simpl in H1. rewrite subst_nil in H1. apply H1.
  + split; try constructor; try tauto;try constructor.
    - pose proof valid_cons x x nil. simpl in H2. apply H2. easy. constructor.
    - intros. inversion H2; inversion H3;subst. inversion H8.
    - intros. inversion H2; subst. tauto. inversion H8. 
  + pose proof aeq_refl_varong [(x,x,true)] M. apply H2.
    repeat constructor. pose proof valid_cons x x nil. simpl in H3. apply H3.
    easy. constructor.
Qed.

Definition set_zero (x:V) (l: list V) (n:nat):=
  if in_vars_dec x l then 0 else n.
  
Lemma set_zero_plus: forall x l a b,
  set_zero x l (a+b) = set_zero x l a + set_zero x l b.
Proof.
  intros. unfold set_zero. destruct (in_vars_dec x l); tauto.
Qed.

Lemma zero_set_zero: forall x l,
  set_zero x l 0 = 0.
Proof.
  intros. unfold set_zero.
  destruct (in_vars_dec x l); reflexivity.
Qed.

Lemma no_set_zero: forall x l n,
  ~ In x l ->
  set_zero x l n = n.
Proof.
  intros. unfold set_zero. destruct (in_vars_dec x l); tauto.
Qed.

Lemma do_set_zero: forall x l n,
   In x l ->
  set_zero x l n = 0.
Proof.
  intros. unfold set_zero. destruct (in_vars_dec x l); tauto.
Qed.

Lemma aeq_free_occur_varong: forall x bd t1 t2,
  alpha_eq bd t1 t2 ->
  set_zero x (binder_l bd) (free_occur x t1) = set_zero x (binder_r bd) (free_occur x t2) .
Proof.
  intros. revert t2 bd H. induction t1; intros; inversion H; subst.
  + simpl. rewrite 2 zero_set_zero. reflexivity. 
  + simpl. destruct (var_eq_dec x s); destruct (var_eq_dec x s2); subst.
    - destruct_eq_dec. assert (H4:=H3). apply in_binder_l in H4. apply in_binder_r in H3.
      rewrite 2 do_set_zero; tauto.
    - apply in_binder_l in H3. rewrite <- var_occur_not_eq_dec in n. 
      rewrite n. rewrite zero_set_zero. rewrite do_set_zero; tauto.
    - apply in_binder_r in H3. rewrite <- var_occur_not_eq_dec in n.
      rewrite n. rewrite zero_set_zero. rewrite do_set_zero; tauto.
    - rewrite <- var_occur_not_eq_dec in n. rewrite <- var_occur_not_eq_dec in n0.
      rewrite n. rewrite n0. rewrite 2 zero_set_zero. reflexivity.
  + simpl. destruct_eq_dec. rewrite 2 no_set_zero; tauto. rewrite 2 zero_set_zero. reflexivity.
  + specialize IHt1_1 with t3 bd. specialize IHt1_2 with t4 bd.
    simpl. rewrite set_zero_plus. rewrite set_zero_plus.
    rewrite IHt1_1; try tauto. rewrite IHt1_2; tauto. 
  +  specialize IHt1 with t3 ((v, x', true) :: update v x' bd).
    destruct_eq_dec. 
    - rewrite 2 zero_set_zero. reflexivity.
    - rewrite zero_set_zero. simpl in IHt1. unfold set_zero at 1 in IHt1.
      destruct (in_vars_dec v (v :: binder_l (update v x' bd))).
      apply IHt1 in H5. clear IHt1.
      rewrite <-update_binder_r in H5. unfold set_zero in H5.
      destruct (in_vars_dec v (x' :: binder_r bd) ). 
      destruct i0. congruence. rewrite do_set_zero; tauto.
      rewrite <- H5. rewrite zero_set_zero. reflexivity.  
      des_notin n0. congruence.
    - rewrite zero_set_zero. simpl in IHt1.
      apply IHt1 in H5. clear IHt1. unfold set_zero at 2 in H5.
      destruct (in_vars_dec x' (x' :: binder_r (update v x' bd))).
      2:{ des_notin n0. congruence. }
      rewrite <- update_binder_l in H5. unfold set_zero in H5.
      destruct (in_vars_dec x' (v :: binder_l bd)).
      destruct i0. congruence. rewrite do_set_zero; tauto. 
      rewrite H5. rewrite zero_set_zero. reflexivity.
    - simpl in IHt1. rewrite <- update_binder_l in IHt1. 
      rewrite <- update_binder_r in IHt1. apply IHt1 in H5. clear IHt1.
      unfold set_zero in H5. destruct (in_vars_dec x (v :: binder_l bd));
      destruct (in_vars_dec x (x' :: binder_r bd)).
      * destruct i. congruence. destruct i0. congruence.
        rewrite 2 do_set_zero; tauto.
      * rewrite <- H5. rewrite zero_set_zero. destruct i. congruence.
        rewrite do_set_zero; tauto.
      * destruct i. congruence. rewrite H5. rewrite zero_set_zero.
        rewrite do_set_zero; tauto.
      * rewrite not_in_cons in n1. rewrite not_in_cons in n2.
        rewrite 2 no_set_zero; tauto.
Qed.

(** Alpha equivalence terms have same free variables **)
Lemma aeq_free_occur: forall x t1 t2,
  t1 =a= t2 ->
  free_occur x t1 = free_occur x t2.
Proof.
  intros. pose proof aeq_free_occur_varong x nil t1 t2.
  simpl in H0. apply H0 in H. rewrite 2 no_set_zero in H; tauto.
Qed.

Instance Proper_free_occur: Proper (eq==>aeq==>eq) free_occur.
Proof. intros ? ? ? ? ? ?. subst y. apply aeq_free_occur. tauto. Qed.

Lemma add_bind_aeq_list_update_lemma: forall s l,
  ~ In s (binder_l l) ->
  ~ In s (binder_r l) ->
  list_update l [(s,s,true)] = [(s,s,true)].
Proof.
  intros. induction l.  tauto.
  destruct a as [[s1 s2] b].
  simpl in H. apply deMorgan1 in H. destruct H.
  simpl in H0. apply deMorgan1 in H0. destruct H0.
  simpl. rewrite IHl; try tauto. simpl. destruct_eq_dec.
Qed.

Lemma add_bind_aeq_varong: forall s l t1 t2,
  alpha_eq l t1 t2 ->
  alpha_eq (l++ list_update l [(s,s,true)]) t1 t2.
Proof.
  intros. revert t2 l H. induction t1; intros; inversion H; subst.
  + constructor.
  + apply str_aeq1. easy. rewrite in_app_iff. tauto.
  + destruct (var_eq_dec s s0).
      - subst s. apply str_aeq1. easy. rewrite in_app_iff. right. 
      rewrite add_bind_aeq_list_update_lemma;[now left|tauto|tauto].
    - apply str_aeq2.
      * rewrite binder_l_app. apply not_in_app. split. tauto.
        rewrite <- list_update_binder_l. simpl. tauto.
      * rewrite binder_r_app. apply not_in_app. split. tauto.
        rewrite <- list_update_binder_r. simpl. tauto.
  + specialize IHt1_1 with t3 l. specialize IHt1_2 with t4 l. constructor; tauto.
  + constructor. easy.
    specialize IHt1 with t3 ((v, x', true) :: update v x' l).
    simpl in IHt1. rewrite update_app. 
    pose proof list_update_var_equal l (update v x' l) [(s,s,true)].
    rewrite H0; [tauto| apply update_var_equal].
Qed.
  
(**  Add the same binder preserves aeq **)  
Corollary add_bind_aeq: forall s t1 t2,
  t1 =a= t2 ->
  (abs s t1) =a= (abs s t2).
Proof. 
  intros. constructor. easy. simpl.
  pose proof add_bind_aeq_varong s nil t1 t2.
  apply H0. exact H.
Qed.

Instance Proper_abs: Proper (eq==>aeq==>aeq) abs.
Proof.
  intros ? ? ? ? ? ?. subst y. apply add_bind_aeq. tauto.
Qed.

Lemma remove_bind_aeq_varong: forall s l t1 t2,
  alpha_eq (l++ list_update l [(s,s,true)]) t1 t2 ->
  alpha_eq l t1 t2.
Proof.
  intros. revert t2 l H. induction t1;intros;inversion H;subst.
  + constructor.
  + rewrite in_app_iff in H3. destruct H3.
      - now apply str_aeq1. 
      - apply true_binder_in_list_updated_list in H0. destruct H0 as [? [? ?]].
         destruct H0. injection H0; intros. subst s2. subst s0.
         apply str_aeq2;tauto. inversion H0. 
  + rewrite binder_l_app in H1. rewrite binder_r_app in H3. apply str_aeq2; solve_notin.
  + specialize IHt1_1 with t3 l. specialize IHt1_2 with t4 l. constructor; tauto.
  + constructor. easy. apply IHt1. simpl. rewrite update_app in H5.
      pose proof list_update_var_equal l (update v x' l) [(s,s,true)].
      rewrite <- H0;[tauto|apply update_var_equal].
 Qed.

Lemma remove_bind_aeq: forall x t1 t2,
  abs x t1 =a= abs x t2 ->
  t1 =a= t2.
Proof.
  intros. pose proof remove_bind_aeq_varong x nil t1 t2.
  simpl in H0. inversion H;subst. simpl in H7. tauto. 
Qed.

Lemma inversion_abs_lemma: forall x y t1 t2,
  x <> y ->
  abs x t1 =a= abs y t2 ->
  t1 =a= subst [(y,var x)] t2.
Proof.
  intros.  inversion H0;subst. simpl in H7.
  pose proof critical t1 t2 nil [(x,y,true)] [None] [Some x].
  simpl in H1. rewrite subst_nil in H1.
  assert (aeq_sub_Assumption t1 t2 [] [(x, y, true)] [None] [Some x] ).
  split; try constructor; try constructor; try reflexivity.
  + pose proof valid_cons x y nil. apply H2. easy. constructor.
  + simpl. intros. inversion H2; subst. inversion H10.
  + simpl. intros. inversion H2;subst. 2:{ inversion H10. }
      pose proof aeq_free_occur x0 (abs x0 t1) (abs y t2). assert (H6:=H0).
      apply H3 in H6. simpl in H6. destruct (var_eq_dec x0 x0) in H6; 
      destruct (var_eq_dec x0 y) in H6; congruence.
  + easy.
  + apply H1 in H7. 
      pose proof (remove_bind_aeq x t1 (subst [(y,var x)] t2)). apply H3. now constructor.
      apply H2.
Qed.

(**  If abs x t1 =a= abs y t2 then t1 =a= t2[y|->x] **)
Lemma inversion_abs: forall x y t1 t2,
  abs x t1 =a= abs y t2 ->
  t1 =a= subst [(y,var x)] t2.
Proof.
  intros. destruct (var_eq_dec x y).
  + subst y. rewrite subst_var_with_itself. apply remove_bind_aeq with x. tauto. 
  + apply inversion_abs_lemma;tauto.
Qed.

(** Tactic that tries to solve equivalence**)  
Ltac aeq_solve:=
    repeat match goal with
     | [H: context[alpha_eq nil ?t1 ?t2] |- _ ] => let ph:=fresh "H" in 
                                                    assert (alpha_eq nil t1 t2 = aeq t1 t2) as ph;
                                                    [reflexivity| rewrite ph in H; clear ph]
     | [|- alpha_eq nil ?t1 ?t2] => let ph:=fresh "H" in 
                                    assert (alpha_eq nil t1 t2 = aeq t1 t2) as ph;
                                    [reflexivity| rewrite ph;clear ph]
     | [H: aeq ?t1 ?t2 |- aeq ?t1 ?t2] => exact H
     | [|- aeq ?t ?t] => reflexivity
     | [H: aeq ?t1 ?t2 |- aeq ?t2 ?t1] => symmetry
     | [|- aeq (abs ?s ?t1) (abs ?s ?t2)] => apply add_bind_aeq
     | [H:aeq (abs ?s ?t1)(abs ?s ?t2) |- aeq ?t1 ?t2] => apply remove_bind_aeq in H;tauto
     | [|- aeq (subst ?st _) (subst ?st _)] => apply subst_same_st_aeq
     | [H: aeq ?t1 ?t2 |- aeq ?t1 ?t3] => transitivity t2;[| clear H]
     | [H: aeq ?t1 ?t2 |- aeq ?t3 ?t1] => transitivity t2;[clear H|]
     | [H: aeq ?t2 ?t1 |- aeq ?t1 ?t3] => transitivity t2;[| clear H]
     | [H: aeq ?t2 ?t1 |- aeq ?t3 ?t1] => transitivity t2;[clear H|]
     | [H: free_occur ?x ?t1 = ?n |- free_occur ?x ?t2 = ?n] => rewrite aeq_free_occur with x t2 t1;[exact H|]
     | [|- free_occur ?s _ = free_occur ?s _] => apply aeq_free_occur
     | [|- aeq (app _ _) (app _ _)] => constructor
     | [|- aeq (cons _) (cons _)] => constructor
     | [|- aeq (abs _ _)(abs _ _)] => constructor
     | [|- aeq (app _ _) (app _ _)] => constructor
     | [|- alpha_eq _ (cons _) (cons _)] => constructor
     | [|- alpha_eq _ (abs _ _)(abs _ _)] => constructor
     | [|- _] => try tauto
    end.  

Fixpoint binder_occur (x:V) (t:tm): bool:=
  match t with
  | cons c => false
  | var s => false
  | app t1 t2 =>  binder_occur x t1 || binder_occur x t2
  | abs s t0 => if (var_eq_dec x s) then true else binder_occur x t0
  end.
  
Lemma binder_occur_in_renamed: forall x z s t,
  ~ In z (tm_var t) ->
  binder_occur x (subst [(s, var z)] t) = true -> 
  binder_occur x t = true.
Proof.
  intros. induction t.
  + inversion H0.
  + inversion H0. destruct_eq_dec.
  + simpl. apply orb_true_intro. simpl in H0. apply orb_true_elim in H0.
    destruct H0.
    - left. apply IHt1; try tauto. simpl in H. apply not_in_app in H. tauto.
    - right. apply IHt2;try tauto. simpl in H. apply not_in_app in H. tauto. 
  + simpl in H0. destruct (var_eq_dec v s).
    - simpl in H0. simpl. rewrite subst_nil in H0. exact H0.
    - simpl in H0. destruct (var_occur_eq v z) in H0. des_notin H. contradiction.  
      simpl in H0. destruct_eq_dec. 
      apply IHt; try tauto. solve_notin.
Qed.


Ltac binder_occur_contract H:=
 match type of H with 
  | forall _ , binder_occur _ (abs ?x ?t) = true -> _  =>
      let ph1:= fresh "H" in let ph2:= fresh "H" in assert (ph1:=H); specialize ph1 with x; 
       assert (binder_occur x (abs x t) = true) as ph2; [simpl; destruct_eq_dec| apply ph1 in ph2; clear ph1]
  end.

(** Any term can be renamed so that its binders do not fall into a certain scope **) 
Theorem variable_convention: forall t xs,
  exists t', t =a= t' /\ (forall x, binder_occur x t' = true -> ~ In x xs).
Proof.
  intros. induction t.
  + exists c. split. constructor. intros. simpl in H. congruence.
  + exists s. split. apply str_aeq2; tauto. intros.
    simpl in H. congruence.
  + destruct IHt1 as [t1' IHt1]. destruct IHt2 as [t2' IHt2]. exists (app t1' t2'). 
    destruct IHt1. destruct IHt2.
    split. constructor; tauto. intros. simpl in H3.
    apply orb_true_elim in H3. destruct H3; auto.
  + destruct IHt as [t' H]. remember (newvar(xs++tm_var t') (varsort v) ) as z.
    exists (abs z (subst [(v,var z)] t')). split.
    - destruct H. apply add_bind_aeq with v t t' in H.
      assert (aeq (abs v t') (abs z (subst [(v, var z)] t'))).
      apply renaming_aeq. subst z. rewrite newvar_sort. easy. solve_notin.
      eapply aeq_trans;[apply H|tauto].
    - intros. simpl in H0. destruct (var_eq_dec x z).
      subst x. solve_notin. destruct H. pose proof binder_occur_in_renamed x z v t'.
      assert (~ In z (tm_var t')) by solve_notin. specialize H1 with x.  tauto.
Qed.

Corollary abs_rename: forall x t xs,
  exists u t', (abs x t) =a= (abs u t') /\ ~ In u xs.
Proof.
  intros. pose proof variable_convention (abs x t) xs.
  destruct H. destruct H. inversion H; subst.
  exists x'. exists t2. specialize H0 with x'.
  split. tauto. apply H0. destruct_eq_dec. 
Qed.

Corollary abs_penetrate: forall s t st,
  exists x t',(subst st (abs s t)) =a= (subst st (abs x t')) /\ 
  subst st (abs x t') = abs x (subst st t') /\ (abs s t) =a= (abs x t').
Proof.
  intros. pose proof abs_rename s t (task_var st). 
  destruct H. destruct H. destruct H. exists x. exists x0.
  split;[|split].  
  + apply subst_same_st_aeq; tauto.
  + apply not_in_task_var_no_st_occur in H0. assert (H2:=H0). apply no_st_occur_zero_no_st_tm_occur in H0. simpl.
      assert (st_tm_occur x (reduce x st) = 0).
      apply reduce_no_st_tm_occur;tauto. rewrite H1.
      rewrite no_reduce. reflexivity. clear H H0 H1.
      induction st. tauto. destruct a.  zero_r H2. 
      rewrite var_occur_not_eq_dec in H2. simpl. apply not_in_cons. split;[congruence|tauto].
  + easy.
Qed.

Definition alpha_compatible P := forall M N,
  M =a= N -> 
  P M ->
  P N.

Ltac use_variable_convention M xs:=
 let ph1:= fresh "H" in let ph2:=fresh "H" in let t1:=fresh "M" in
   pose proof variable_convention M xs as ph; destruct ph as [t1 [ph1 ph2]].
   
Ltac rename_tm M  M':=
  repeat match goal with
  | [H:context [M'] |- _] => clear H
  end; clear M';  rename M into M'.

Theorem alpha_induction: forall (P: tm -> Prop) xs,  
  alpha_compatible P ->
  (forall c, P (cons c)) ->
  (forall x, P (var x)) ->
  (forall M N, P M -> P N -> P (app M N)) ->
  (forall x t, ~ In x xs -> P t -> P (abs x t)) ->
  (forall t, P t).
Proof.
  intros P xs compP Hc Hv Happ Habs t.
  use_variable_convention t xs.
  symmetry in H.
  cut (P M).
  now apply compP.
  clear t H.
  induction M; intros; auto.
  + apply Happ.
    - apply IHM1. intros.
      apply H0.
      simpl. rewrite H. apply orb_true_l.
    - apply IHM2. intros.
      apply H0.
      simpl. rewrite H. apply orb_true_r.
  + apply Habs. apply H0. destruct_eq_dec. 
    apply IHM. intros.
    apply H0.
    destruct_eq_dec.
Qed.

Lemma subst_not_free_variable_is_still_aeq: forall x M t,
  free_occur x M = 0 ->
  M =a= (subst [(x,t)] M).
Proof.
  intros x M t. 
  apply alpha_induction with (xs:= task_var[(x,t)])(t:=M); intros.
  + unfold alpha_compatible. intros.
    assert (free_occur x M0 = 0) by aeq_solve.
    apply H0 in H2. assert (H':=H). aeq_solve. 
  + reflexivity. 
  + simpl in H. rewrite var_occur_not_eq_dec in H. destruct_eq_dec. aeq_solve.
  + zero_r H1. simpl. aeq_solve.
  + des_notin H.
    assert (free_occur x0 t = 0) by solve_notin.
    destruct_eq_dec. simpl.
    aeq_solve.
    apply H0. simpl in H1. destruct_eq_dec.  
Qed.


Lemma subst_an_aeq_term_is_still_aeq_lemma: forall x bd M M' N N',
  (forall s, binder_occur s M  = true -> ~ In s (x::tm_var N ++ tm_var N')) ->
  (forall s, binder_occur s M' = true -> ~ In s (x::tm_var N ++ tm_var N')) ->
  (forall s, In s (binder_l bd) -> ~ In s (x::tm_var N ++ tm_var N')) ->
  (forall s, In s (binder_r bd) -> ~ In s (x::tm_var N ++ tm_var N')) ->
  alpha_eq bd M M' ->
  aeq N N' ->
  alpha_eq bd (subst [(x,N)] M) (subst [(x,N')] M').
Proof.
  intros. induction H3;simpl.
  + constructor.
  + assert (s1<>x).
     specialize H1 with s1. apply in_binder_l in H5. apply H1 in H5. solve_notin.
     assert (s2<>x).
     specialize H2 with s2. apply in_binder_r in H5. apply H2 in H5. solve_notin.
     destruct_eq_dec. clear n n0. apply str_aeq1. easy. tauto. 
  + destruct_eq_dec.  
    - pose proof irrelevant_binder_aeq nil bd N N'.
      simpl in H6. apply H6.
      * intros. apply H1 in H7. solve_notin.
      * intros. apply H2 in H7. solve_notin.
      * tauto.
    - apply str_aeq2; tauto.
  + constructor.
    - apply IHalpha_eq1. intros.
      assert (binder_occur s (app t1 t2)= true).
      simpl. rewrite H3. rewrite orb_true_l. reflexivity. specialize H with s. tauto. 
      intros. assert (binder_occur s (app t3 t4)=true). simpl. rewrite H3.
      rewrite orb_true_l. reflexivity. specialize H0 with s. tauto.
      exact H1. exact H2.
    - apply IHalpha_eq2. intros.
      assert (binder_occur s (app t1 t2)= true).
      simpl. rewrite H3. rewrite orb_true_r. reflexivity. specialize H with s. tauto. 
      intros. assert (binder_occur s (app t3 t4)=true). simpl. rewrite H3.
      rewrite orb_true_r. reflexivity. specialize H0 with s. tauto.
      exact H1. exact H2.
  + assert (x0<>x). binder_occur_contract H. solve_notin.
    assert (x'<>x). binder_occur_contract H0. solve_notin.
    destruct_eq_dec. clear n n0.
    assert (alpha_eq ((x0, x', true) :: update x0 x' bd) (subst [(x, N)] t1)
               (subst [(x, N')] t2)).
    { apply IHalpha_eq. intros. destruct (var_eq_dec s x0).
    subst s. binder_occur_contract H. tauto.
    apply H. specialize H with s. simpl. destruct_eq_dec.
    intros. destruct (var_eq_dec s x').  subst s. 
    binder_occur_contract H0. tauto. apply H0. simpl. destruct_eq_dec.
    intros. simpl in H8. rewrite <-update_binder_l in H8. destruct H8.
    subst s. binder_occur_contract H. tauto. now apply H1. 
    intros. simpl in H8. rewrite <-update_binder_r in H8. destruct H8.
    subst s. binder_occur_contract H0. tauto. now apply H2.  } 
    clear IHalpha_eq.
    binder_occur_contract H.  assert (free_occur x0 N=0) by solve_notin. 
    binder_occur_contract H0.  assert (free_occur x' N'=0) by solve_notin.
    rewrite H9. rewrite H11. now constructor. 
Qed.

(** If M=a=M' N=a=N', then M[x|->N]=a=M'[x|->N']**)
Theorem subst_an_aeq_term_is_still_aeq: forall x M M' N N',
  M =a= M' ->
  N =a= N' ->
  subst [(x, N)] M =a= subst [(x, N')] M'.
Proof.
  intros. use_variable_convention M (x::tm_var N++tm_var N').
  use_variable_convention M' (x::tm_var N++tm_var N').
  transitivity (subst [(x,N)] M0);[aeq_solve|].
  transitivity (subst [(x,N')] M1);[|aeq_solve].
  assert (M0 =a= M1) by aeq_solve.
  rename_tm M0 M. rename_tm M1 M'.
  pose proof subst_an_aeq_term_is_still_aeq_lemma x nil M M' N N'.
  apply H; tauto. 
Qed.
     

Lemma no_free_occur_if_var_is_substed: forall x M N,
  free_occur x N = 0 ->
  free_occur x (subst [(x,N)] M) = 0.
Proof.
  intros.
  apply alpha_induction with (xs:= task_var [(x,N)]) (t:=M); intros.
  + unfold alpha_compatible. intros.
    aeq_solve.
  + reflexivity.
  + destruct_eq_dec.
  + simpl. rewrite H0. rewrite H1. reflexivity. 
  + assert (free_occur x0 N = 0) by solve_notin.
    destruct_eq_dec. 
Qed.
  
(** If free_occur x L = 0, then M[x|->N][y|->L] =a= M[y|->L][x|-> N[y|->L] ]**)  
Lemma substitution_lemma: forall x y M N L,
  x <> y ->
  free_occur x L = 0 ->
  subst [(y,L)] (subst [(x,N)] M) =a= subst ([(x,subst [(y,L)] N)]) (subst [(y,L)] M).
Proof.
  intros x y M N L. 
  apply alpha_induction with (xs:= task_var [(x,N)] ++ task_var [(y,L)]) (t:=M); intros.
  + unfold alpha_compatible. intros.
    specialize (H0 H1 H2).
    transitivity (subst [(y, L)] (subst [(x, N)] M0)); aeq_solve.
  + constructor.
  + destruct_eq_dec;simpl;destruct_eq_dec;try aeq_solve.
    apply subst_not_free_variable_is_still_aeq with x L (subst [(y, L)] N) in H0. tauto.
  + simpl. aeq_solve. 
  + assert (x0 <> x) by solve_notin. assert (x0 <> y) by solve_notin.
    assert (free_occur x0 N = 0) by solve_notin.
    assert (free_occur x0 L = 0) by solve_notin.
    repeat destruct_eq_dec. 
    assert(st_tm_occur x0 [(y,L)] = 0) by solve_notin.
    assert (free_occur x0 (subst [(y, L)] N) = 0).
    {
      apply subst_keep_no_free_occur; solve_notin.
    } 
    rewrite H8. simpl. aeq_solve.
Qed.


(** t[x|->y][y|->x]=a=t**)
Lemma subst_var_and_rollback_aeq: forall x y t,
  free_occur y t = 0 ->
  subst [(y,var x)] (subst [(x, var y)] t) =a= t.
Proof.
  intros x y t.
  apply alpha_induction with (xs:= [x;y]) (t:=t); intros.
  + unfold alpha_compatible. intros. assert (H':=H).
    assert (free_occur y M = 0) by aeq_solve.
    apply H0 in H2.
    clear H0 H1.
    transitivity (subst ((y,var x)::nil) (subst ((x, var y)::nil) M)).
    aeq_solve.
    aeq_solve.
  + simpl. aeq_solve.
  + repeat destruct_eq_dec.
     - aeq_solve.
     - unfold free_occur in H.  destruct_eq_dec.
     - aeq_solve.
  + zero_r H1. simpl. aeq_solve. 
  + assert (y <> x0) by solve_notin. zero_r H1. destruct_eq_dec. assert (x<>x)  by solve_notin. congruence. 
    simpl. repeat destruct_eq_dec. aeq_solve. 
Qed.

(** If t1=a=t2[y|->x], then abs x t1 =a= abs y t2 **)
Lemma add_different_bind_aeq: forall x y t1 t2,
  varsort x = varsort y ->
  free_occur x t2 = 0 ->
  t1 =a= subst [(y, var x)] t2 ->
  abs x t1 =a= abs y t2.
Proof.
  intros. destruct (var_eq_dec x y).
  + subst y. apply add_bind_aeq. now rewrite subst_var_with_itself in H1. 
  + pose proof subst_var_and_rollback_aeq y x t2. apply H2 in H0; clear H2.
      transitivity (abs y (subst [(x, var y)] (subst [(y,var x)] t2)));[|aeq_solve].
      pose proof critical t1 (subst [(y, var x)] t2) nil [(x,x,true)] [None] [Some y].
      simpl in H2. rewrite subst_nil in H2. constructor. easy. apply H2.
      split; simpl;try constructor;try constructor;try reflexivity.
      - pose proof valid_cons x x nil. apply H3. easy. constructor.
      - intros. inversion H3;subst. inversion H9.
      - intros. inversion H3;subst. apply no_free_occur_if_var_is_substed. destruct_eq_dec. inversion H9.
      - easy.
      - pose proof add_bind_aeq_varong x nil t1 (subst [(y, var x)] t2). tauto.
Qed.

(**  t[x|->M][x|->N] =a= t[x|->M[x|->N]] **)
Lemma subst_one_var_twice_aeq: forall x M N t,
  subst [(x,N)] (subst [(x,M)] t) =a= subst [(x, subst [(x,N)] M)] t.
Proof.
  intros. apply alpha_induction with (xs:= x::tm_var M ++ tm_var N) (t:=t); intros.
  + unfold alpha_compatible; intros. 
    transitivity  (subst [(x, N)] (subst [(x, M)] M0));aeq_solve.
  + simpl. aeq_solve.
  + destruct_eq_dec; aeq_solve. 
  + simpl. aeq_solve. 
  + des_notin H. assert (free_occur x0 M = 0) by solve_notin.
    repeat destruct_eq_dec.
    assert ( free_occur x0 N = 0) by solve_notin.
    repeat destruct_eq_dec.
    assert (free_occur x0 (subst [(x, N)] M) = 0). 
    apply subst_keep_no_free_occur; solve_notin.
    simpl. apply deMorgan2. rewrite <- app_nil_end. tauto.
    rewrite H5. simpl. aeq_solve. 
Qed.

(** If free_occur y M=0, then M[x|->t]=a=M[x|->y] [y|->t]**)
Lemma subst_var_trivial_renaming: forall x y t M,
  free_occur y M = 0 ->
  subst [(x,t)] M =a= subst [(y,t)] (subst [(x, var y)] M).
Proof.
  intros x y t M.
  apply alpha_induction with (xs:=x::y::tm_var t)(t:=M); intros. 
  + unfold alpha_compatible; intros.
    transitivity (subst [(x, t)] M0);[aeq_solve|].
    transitivity (subst [(y, t)] (subst [(x,var y)] M0));[|aeq_solve].
    apply H0. aeq_solve.
  + simpl. aeq_solve.
  + destruct_eq_dec. aeq_solve. cbv in H. destruct_eq_dec. aeq_solve.
  + zero_r H1. simpl. aeq_solve. 
  + des_notin H.
    simpl in H1.
    assert (free_occur x0 t = 0) by solve_notin.
    repeat destruct_eq_dec. aeq_solve.
Qed.

Lemma aeq_rank: forall M N,
  M =a= N ->
  rank M = rank N.
Proof.  intros. induction H; try reflexivity; simpl; congruence. Qed.

Instance Proper_rank: Proper (aeq==>eq) rank.
Proof.
  intros ? ? ?. apply aeq_rank. tauto.
Qed.
 
Lemma subst_task_is_var_rank_eq: forall M st,
  Forall is_var (range st) ->
  rank M = rank (subst st M).
Proof.
  intros. generalize dependent st.
  induction M;intros.
  + reflexivity.
  + pose proof st_is_var_sub_is_var s st. apply H0 in H.
      inversion H;subst. simpl. rewrite <- H2. reflexivity.
  + simpl. rewrite <- IHM1; try tauto. rewrite <- IHM2; tauto.
  + simpl. destruct (st_tm_occur v (reduce v st)); simpl; f_equal; apply IHM.
      - apply is_var_reduce; tauto.
      - simpl. apply Forall_cons_iff.
        split;[constructor| apply is_var_reduce;tauto].
Qed.
      
Lemma subst_destruct_aeq: forall x s st M,
  ~ In s (domain st) ->
  subst ((x, var s)::st) M =a= subst st (subst [(x, var s)]  M). 
Proof.
  intros. 
  use_variable_convention M (x::s::task_var st).
  transitivity (subst ((x,var s)::st) M0);[aeq_solve|].
  transitivity (subst st (subst [(x, var s)] M0));[|aeq_solve].
  rename_tm M0 M. generalize dependent st.
  induction M; intros.
  + simpl. aeq_solve.
  + destruct_eq_dec.
      - simpl. rewrite str_not_in_domain_then_var_sub_is_self;[aeq_solve| tauto].
      - simpl. aeq_solve.
  + simpl. constructor.
      - apply IHM1.  tauto. intros. apply H1. simpl. rewrite H0. apply orb_true_l.
      - apply IHM2.  tauto. intros. apply H1. simpl. rewrite H0. apply orb_true_r.
  + simpl.  binder_occur_contract H1. 
    assert (v<>x) by solve_notin.
    destruct_eq_dec.
    des_notin H2. congruence.
    assert (st_tm_occur v (reduce v st) = 0).
    apply reduce_no_st_tm_occur.
    solve_notin.
    rewrite H3.
    aeq_solve.
    apply IHM.
    apply not_in_domain_reduce_other; auto.
    intros. 
    specialize H1 with x0.
    simpl binder_occur in H1.
    destruct_eq_dec; solve_notin.
    - now apply not_in_task_var_not_in_reduced_task_var.
    - specialize (H1 H4).
      assert (~ In x0 (task_var st)) by tauto.
      now apply not_in_task_var_not_in_reduced_task_var.
Qed.

Lemma subst_destruct_equal: forall x y z P,
  ~ In z (x::y::tm_var P) ->
  subst ((y,var z)::(x, var y)::nil) P = subst [(x, var y)] (subst [(y,var z)] P).
Proof.
  intros. assert (x<>z) by solve_notin.
  assert (y<>z) by solve_notin. induction P.
  + reflexivity.
  + assert (z<>s) by solve_notin. repeat destruct_eq_dec.
  + simpl. rewrite IHP1;[|solve_notin]. rewrite IHP2;[reflexivity|]. repeat solve_notin. 
  + assert (z<>v) by solve_notin. repeat destruct_eq_dec; try rewrite subst_nil; try reflexivity.
      - rewrite subst_nil. reflexivity.
      -  f_equal. apply IHP. solve_notin.
Qed.


(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Church Rosser                                               *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Inductive beta_reduction: relation tm:=
  | beta_reduction_constructor: forall x M N,
    beta_reduction (app (abs x M) N) (subst [(x,N)] M)
.

Definition compatible (R:relation tm):=
  forall x M N Z, R M N -> R (app Z M) (app Z N) /\ R (app M Z) (app N Z) /\ R (abs x M) (abs x N).

(** Compatible closure **)                                                            
Inductive clos_comp (R: relation tm): relation tm:=
 | cp_step: forall M N,
    R M N ->
    clos_comp R M N
    
 | cp_app_r: forall M N Z,
    clos_comp R M N ->
    clos_comp R (app Z M) (app Z N)
    
 | cp_app_l: forall M N Z,
    clos_comp R M N ->
    clos_comp R (app M Z) (app N Z)
    
 | cp_abs: forall x M N,
    clos_comp R M N ->
    clos_comp R (abs x M) (abs x N) 
.

Definition clos_comp_refl_trans (R: relation tm) : relation tm:=
 clos_refl_trans tm (clos_comp R).
 
Lemma clos_refl_trans_refl: forall {X} R, Reflexive (clos_refl_trans X R).
Proof.  intros. constructor 2. Qed.

Lemma clos_refl_trans_trans: forall {X} R, Transitive (clos_refl_trans X R).
Proof.  unfold Transitive. intros. constructor 3 with y; tauto. Qed.

Add Parametric Relation (X:Type)(R: relation X): X (clos_refl_trans X R) reflexivity proved by (clos_refl_trans_refl R)
        transitivity proved by (clos_refl_trans_trans R) as clos_refl_trans_refl_trans.

Add Parametric Relation (R: relation tm): tm (clos_comp_refl_trans R) reflexivity proved by (clos_refl_trans_refl (clos_comp R))
        transitivity proved by (clos_refl_trans_trans (clos_comp R))  as crt_refl_trans.
        
        
(** Diamond property that explicitily includes alpha_equivalence **)
Definition diamond (R: relation tm):=
  forall M M1 M2, 
    R M M1 ->
    R M M2 ->
    exists M3 M4, R M1 M3 /\ R M2 M4 /\ M3=a=M4.

(** A relation is CR if is compatible, relfexive, transitive closure satisfires diamond property**)
Definition CR (R: relation tm):=
  diamond (clos_comp_refl_trans R).

(** An important property about alpha_equivalence**)
Definition preserve_aeq (R: relation tm):=
  forall M M' N, R M M' -> M =a= N -> exists N', R N N' /\ N' =a= M'.    
  
Lemma same_relation_iff: forall {X:Type} A B,
  same_relation X A B <-> forall x y, A x y <-> B x y.
Proof.
  split; intros.  
  + cbv in H. destruct H. split; auto. 
  + cbv. split; intros; apply H;tauto.
Qed.   
  
Instance Proper_clos_comp: Proper (same_relation tm ==> same_relation tm) clos_comp.
Proof.
  intros ? ? ?. apply same_relation_iff. rewrite same_relation_iff in H. intros.
  split; intros. 
  + induction H0; subst.
      - constructor. apply H. tauto.
      - constructor 2. tauto.
      - constructor 3. tauto.
      - constructor 4. tauto.
  + induction H0; subst.
      - constructor. apply H. tauto.
      - constructor 2. tauto.
      - constructor 3. tauto.
      - constructor 4. tauto.
Qed. 

Instance Proper_clos_refl_trans: Proper (same_relation tm ==> same_relation tm) (clos_refl_trans tm).
Proof.
  intros ? ? ?. apply same_relation_iff. rewrite same_relation_iff in H. intros.
  split; intros. 
  + induction H0; subst.
      - constructor. apply H. tauto.
      - constructor 2.
      - econstructor 3. apply IHclos_refl_trans1. tauto.
  + induction H0; subst.
      - constructor. apply H. tauto.
      - constructor 2. 
      - econstructor 3. apply IHclos_refl_trans1. tauto.
Qed. 
  
Instance Proper_crt: Proper (same_relation tm ==> same_relation tm) clos_comp_refl_trans.
Proof.
 intros ? ? ?. unfold clos_comp_refl_trans. apply Proper_clos_refl_trans. apply Proper_clos_comp. tauto.
Qed.  
  
Instance Proper_diamond: Proper (same_relation tm ==> iff) diamond.
Proof.
  intros ? ? ?. rewrite same_relation_iff in H. unfold diamond. split; intros;
  specialize H0 with M M1 M2; destruct H0 as [M3 [M4 [? [? ?]]]];try apply H;try tauto;
  exists M3; exists M4. split;[apply H; tauto|split;[apply H; tauto|tauto]].
 split;[apply H; tauto|split;[apply H; tauto|tauto]].
Qed.

Instance Proper_CR: Proper (same_relation tm ==> iff) CR.
Proof. intros ? ? ?. unfold CR. rewrite H. reflexivity. Qed.
  
Lemma trans_preseve_aeq: forall R,
  preserve_aeq R ->
  preserve_aeq (clos_trans tm R).
Proof.
  unfold preserve_aeq. intros.  rewrite clos_trans_tn1_iff in H0. induction H0.
  + specialize H with M y N. destruct H as [? [? ?]]; try tauto. exists x. 
      split. now constructor 1. easy.
  + remember y as M'. subst y. destruct IHclos_trans_n1 as [N' [? ?]].
      specialize H with M' z N'. destruct H as [z' [? ?]]. tauto. aeq_solve. exists z'.
      split.  rewrite clos_trans_tn1_iff. econstructor 2. apply H. now  rewrite <- clos_trans_tn1_iff. easy.
Qed. 
      
Lemma trans_diamond_lemma: forall R x y z,
  diamond R ->
  preserve_aeq R ->
  R x y ->
  clos_trans tm R x z ->
  exists t1 t2, clos_trans tm R y t1 /\ R z t2 /\ t1=a=t2.
Proof.
  intros. unfold diamond in H. 
  apply clos_trans_tn1 in H2.  induction H2.
  + specialize H with x y y0. apply H in H2; try tauto. 
      destruct H2 as [? [? ?]]. exists x0. exists x1. split. rewrite clos_trans_tn1_iff .  eapply tn1_step. tauto. tauto.
  + destruct IHclos_trans_n1 as [t0 [t1 H4]]. destruct H4.
    rewrite clos_trans_tn1_iff in H4. specialize H with y0 z t1. destruct H5. apply H in H2;try tauto. 
    destruct H2 as [M4 [M3 [? [? ?]]]]. unfold preserve_aeq in H0. 
    specialize H0 with t1 M3 t0. apply H0 in H7; try aeq_solve. destruct H7 as [M3' [? ?]].  
    exists M3'. exists M4. split. rewrite clos_trans_tn1_iff. econstructor 2. apply H7. tauto.
    split. tauto. aeq_solve.
Qed.

(**  If a relation satiesfies diamond, so does its transitive closure**)
Lemma trans_diamond: forall R,
  preserve_aeq R -> diamond R -> diamond (clos_trans tm R).
Proof.
  unfold diamond. intros.  revert M2 H2. 
  rewrite clos_trans_tn1_iff in H1.  induction H1; intros.
  + pose proof trans_diamond_lemma R M y M2.
      apply H3 in H1; try tauto. clear H3. destruct H1 as [? [? [? ?]]].
      exists x. exists x0.  split.  tauto. split. constructor 1. tauto. tauto.
  + specialize IHclos_trans_n1 with M2. destruct IHclos_trans_n1 as [M3 [M4 [? ?]]]. tauto.
      destruct H5. pose proof trans_diamond_lemma R y z M3. destruct H7 as [M3' [M3'' [? [? ?]]]]; try tauto.
      unfold preserve_aeq in H. specialize H with M3 M3'' M4. destruct H as [M4' [? ?]]; try tauto.
      exists M3'. exists M4'. split. tauto. split. rewrite clos_trans_tn1_iff. econstructor 2. apply H. 
      rewrite <- clos_trans_tn1_iff. tauto. aeq_solve.
Qed.   

Lemma clos_comp_compatible: forall R,
  compatible (clos_comp R).
Proof.
  unfold compatible. intros.
  split;[|split].
  + constructor 2. tauto.
  + constructor 3. tauto.
  + constructor 4. tauto.
Qed.

Lemma crt_compatible: forall R,
  compatible (clos_comp_refl_trans R).
Proof.
  unfold compatible. intros. induction H;subst.
  + split;[constructor; apply clos_comp_compatible;tauto|
    split;constructor;apply clos_comp_compatible;tauto].
  + split; [reflexivity|split; reflexivity].
  + split;[|split].
      transitivity (app Z y);tauto.
      transitivity (app y Z);tauto.
      transitivity (abs x y); tauto.
Qed.
 
Ltac destruct_compatible H x M N Z n H':=
unfold compatible in H; specialize H with x M N Z;
apply H in H'; clear H; 
match n with
| 1 => let ph := fresh "H" in destruct H' as [H' ph]; clear ph
| 2 => let ph := fresh "H" in let ph2 := fresh "H" in destruct H' as [H' [ph ph2]]; clear H' ph2
| 3 => let ph := fresh "H" in let ph2 := fresh "H" in destruct H' as [H' [ph ph2]]; clear H' ph
end. 

(**  The compatible, reflexive, transitive closure of beta reduction  (-> β  star) **)
Definition bstar:= clos_comp_refl_trans beta_reduction.

(** Parallel_reduction for proof  (->>)**)
Inductive parallel_reduction: relation tm:=
| pr_refl: forall M,
    parallel_reduction M M
    
| pr_abs: forall x M M',
    parallel_reduction M M' ->
    parallel_reduction (abs x M) (abs x M')
    
| pr_app: forall M M' N N',
    parallel_reduction M M' ->
    parallel_reduction N N' ->
    parallel_reduction (app M N) (app M' N')
    
| pr_contract: forall x M M' N N',
    parallel_reduction M M' ->
    parallel_reduction N N' ->
    parallel_reduction (app (abs x M) N )  (subst [(x, N')] M') 
.

Lemma abs_pr_inversion: forall x M N,
  parallel_reduction (abs x M) N -> 
  exists N', N = abs x N' /\ parallel_reduction M N'.
Proof.
  intros. inversion H; subst.
  + exists M. split. easy. constructor.
  + exists M'. split. easy. auto.
Qed.

Lemma app_pr_inversion: forall M N L,
  parallel_reduction (app M N) L -> 
  (exists M' N', L = app M' N' /\ parallel_reduction M M' /\ parallel_reduction N N') \/
  (exists x P P' N', M = abs x P /\ L = subst [(x, N')] P' /\ parallel_reduction P P' /\ parallel_reduction N N').
Proof.
  intros. inversion H; subst.
  + left. exists M. exists N. split. easy. split; constructor.
  + left. exists M'. exists N'. tauto.
  + right. exists x. exists M0. exists M'. exists N'. tauto. 
Qed.

Theorem pr_rank_induction: forall (P:tm->tm->Prop), 
  (forall M, P M M) ->
  (
    forall x M M', 
    (forall L L', rank L <= rank M -> parallel_reduction L L' -> P L L') -> 
    parallel_reduction M M' -> 
    P (abs x M) (abs x M')
  ) ->
  (
    forall M1 M1' M2 M2', 
    (forall L L', rank L <= rank M1 -> parallel_reduction L L' -> P L L') ->
    (forall L L', rank L <= rank M2 -> parallel_reduction L L' -> P L L') ->
    parallel_reduction M1 M1' ->
    parallel_reduction M2 M2' ->
    P (app M1 M2) (app M1' M2')
  ) ->
  (
    forall x M M' N N', 
    (forall L L', rank L <= rank M -> parallel_reduction L L' -> P L L') ->
    (forall L L', rank L <= rank N -> parallel_reduction L L' -> P L L') ->
    parallel_reduction M M' ->
    parallel_reduction N N' ->
    P (app (abs x M) N) (subst [(x, N')] M')
  ) ->
  forall M N, parallel_reduction M N -> P M N.
Proof.
  intros. generalize dependent N.
  apply rank_induction with (t:=M).
  intros. destruct t.
  + inversion H4. subst. apply H.
  + inversion H4. subst. apply H.
  + apply app_pr_inversion in H4. destruct H4.
    - destruct H4 as [t1' [t2' [? [? ?]]]]. subst.
      apply H1; auto; intros.
      * apply H3; auto. simpl. pose proof lt_app_rank_l t1 t2. pose proof rank_positive t2. lia.
      * apply H3; auto. simpl. pose proof lt_app_rank_r t1 t2. pose proof rank_positive t1. lia.
    - destruct H4 as [x [t1' [t2' [t3' [? [? [? ?]]]]]]]. subst.
      apply H2; auto; intros.
      * apply H3; auto. simpl. lia. 
      * apply H3; auto. simpl. lia.
  + apply abs_pr_inversion in H4. destruct H4 as [t' [? ?]]. subst.
    apply H0; auto; intros.
    apply H3; auto. simpl. lia.
Qed.

Lemma pr_keep_no_free_occur: forall x M N,
  parallel_reduction M N ->
  free_occur x M = 0 ->
  free_occur x N = 0.
Proof.
  intros. induction H.
  + tauto.
  + simpl in H0. destruct_eq_dec.
  + simpl. zero_r H0.
      apply IHparallel_reduction1 in H0.
      apply IHparallel_reduction2 in H2.  rewrite H0. rewrite H2. reflexivity.
  + zero_r H0. destruct_eq_dec. 
      apply no_free_occur_if_var_is_substed; tauto.
      apply IHparallel_reduction1 in H0; clear IHparallel_reduction1.
      apply IHparallel_reduction2 in H2; clear IHparallel_reduction2.
      apply subst_one_term_keep_no_free_occur; tauto.
Qed.    

Lemma subst_keep_pr_same_subst_var_aeq_lemma1: forall x y z M N,
  x<>y ->
  x<>z ->
  y<>z ->
  free_occur z M = 0 ->
  subst [(z, subst [(x, var y)] N)] (subst [(x, var y)] (subst [(y, var z)] M)) =a=
  subst [(x, var y)] (subst [(y,N)] M).
Proof.
  intros x y z M N ? ? ?.
  apply alpha_induction with (xs:= x::y::z::tm_var N) (t:=M); intros.
  + unfold alpha_compatible. intros.
    assert (free_occur z M0 = 0) by aeq_solve.
    apply H3 in H5.
    transitivity (subst [(z, subst [(x, var y)] N)] (subst [(x, var y)] (subst [(y, var z)] M0)));[aeq_solve|].
    transitivity (subst [(x, var y)] (subst [(y,N)] M0));[|aeq_solve].
    aeq_solve.
  + simpl. aeq_solve.
  + repeat destruct_eq_dec; aeq_solve. simpl in H2. destruct_eq_dec.
  + zero_r H4. simpl. aeq_solve. 
  + simpl. des_notin H2. repeat destruct_eq_dec.  
    assert (free_occur x0 N=0) by solve_notin.
    repeat destruct_eq_dec.
    assert (free_occur x0 (subst [(x, var y)] N)=0).
        { apply subst_one_term_keep_no_free_occur. tauto. destruct_eq_dec. }
    rewrite H9. simpl. aeq_solve. 
    apply H3. simpl in H4. destruct_eq_dec.  
Qed.

Lemma subst_keep_pr_same_subst_var_aeq_lemma2: forall x y z1 z2 M,
  x<>z1 ->
  y<>z1 ->
  x<>z2 ->
  y<>z2 ->
  x<>y ->
  free_occur z1 M = 0 ->
  free_occur z2 M = 0 ->
  subst [(x, var y)] (subst [(y,var z1)] M) =a= subst [(z2,var z1)] (subst [(x,var y)] (subst [(y,var z2)] M)).
Proof.
  intros x y z1 z2 M H H0 H1 H2.
  apply alpha_induction with (xs:= x::y::z1::z2::nil) (t:=M); intros. 
  + unfold alpha_compatible. intros.
    transitivity (subst [(x,var y)] (subst [(y,var z1)] M0));[aeq_solve|].
    transitivity (subst [(z2,var z1)] (subst [(x,var y)] (subst [(y,var z2)] M0)));[|aeq_solve].
    apply H4; aeq_solve.
  + simpl. aeq_solve.
  + repeat destruct_eq_dec;try aeq_solve. cbv in H5. destruct_eq_dec. 
  + zero_r H7. zero_r H6. simpl. aeq_solve. 
  + des_notin H3. repeat destruct_eq_dec.
    aeq_solve.
    apply H4; auto. simpl in H6. destruct_eq_dec. simpl in H7. destruct_eq_dec.
Qed.


(** If M->>M', then exists E, M[x|->y] ->>E /\ E=a=M'[x|->y] **)
Lemma subst_keep_pr_same_subst_var: forall x y M M',
  parallel_reduction M M' ->
  exists E, parallel_reduction (subst [(x, var y)] M)  E /\ E=a=(subst [(x, var y)] M').
Proof.
  intros. revert x y. apply pr_rank_induction with (M:=M) (N:=M'); auto; intros.
  + exists (subst [(x, var y)] M0). split;[constructor|aeq_solve].
  + simpl. destruct_eq_dec. 
    - rewrite 2 subst_nil. exists (abs x0 M'0). split;[ now constructor| aeq_solve ] .
    - remember (newvar (y :: tm_var M0 ++ [x0; y]) (varsort y)) as z1. 
      remember (newvar (y :: tm_var M'0 ++ [x0; y]) (varsort y)) as z2.
      rewrite 2 subst_destruct_equal;try solve_notin.
      pose proof (H0 M0 M'0 (le_n _) H1 y z1) as H2.
      destruct H2 as [t1 [? ?]].
      specialize (H0 (subst [(y, var z1)] M0) t1).
      specialize H0 with (x:=x0)(y:=y).
      destruct H0 as [t2 [? ?]]; auto. 
      {
        rewrite <- subst_task_is_var_rank_eq.
        constructor. repeat constructor.
      }
      exists (abs z1 t2). split. now constructor. 
      assert (t2=a= subst [(x0, var y)] (subst [(y, var z1)] M'0)) by aeq_solve.
      destruct (var_eq_dec z1 z2). rewrite <-e. aeq_solve.
      apply add_different_bind_aeq.
      * subst z1. subst z2. now repeat rewrite newvar_sort. 
      * apply subst_one_term_keep_no_free_occur. apply subst_one_term_keep_no_free_occur.
        apply pr_keep_no_free_occur with (M:=M0). tauto. solve_notin.
        destruct_eq_dec. solve_notin.
      * transitivity (subst [(x0, var y)] (subst [(y,var z1)] M'0));[aeq_solve|].
        apply subst_keep_pr_same_subst_var_aeq_lemma2;subst z1; subst z2.
        solve_notin. solve_notin. solve_notin. solve_notin. congruence.
        apply pr_keep_no_free_occur with (M:=M0). tauto. solve_notin. solve_notin. 
   - specialize (H0 M0 M'0 (le_n _) H1 x0 y). destruct H0 as [E [? ?]]. 
     exists (abs x E). split. now constructor. aeq_solve.
  + specialize (H0 _ _ (le_n _) H2 x y).
    specialize (H1 _ _ (le_n _) H3 x y).
    destruct H0 as [E1 [? ?]]. destruct H1 as [E2 [? ?]].
    exists (app E1 E2). split. now constructor. simpl. aeq_solve.
  + destruct_eq_dec.
    - rewrite subst_nil. specialize (H1 N N' (le_n _) H3 x0 y). 
      destruct H1 as [N'' [? ?]]. 
      exists (subst [(x0,N'')] M'0). repeat constructor; auto.
      transitivity (subst [(x0, subst [(x0, var y)] N' )] M'0);[|symmetry;apply subst_one_var_twice_aeq].
      apply subst_an_aeq_term_is_still_aeq; aeq_solve.
    - remember (newvar (y :: tm_var M0 ++ [x0; y]) (varsort y)) as z.
      rewrite subst_destruct_equal. 2: solve_notin.
      pose proof (H0 M0 M'0 (le_n _) H2 y z) as H4. 
      destruct H4 as [E1' [? ?]].
      specialize (H0 (subst [(y, var z)] M0) E1').
      specialize H0 with (x:=x0) (y:=y). 
      destruct H0 as [E1 [? ?]]; auto. 
      {
        rewrite <- subst_task_is_var_rank_eq. auto.
        repeat constructor. 
      }
      specialize (H1 N N' (le_n _) H3 x0 y). 
      destruct H1 as [E2 [? ?]]. 
      exists (subst [(z,E2)] E1). split. now constructor. 
      transitivity (subst [(z, E2)] (subst [(x0,var y)] (subst [(y,var z)] M'0)));[aeq_solve|].
      transitivity (subst [(z, (subst [(x0,var y)] N'))] (subst [(x0,var y)] (subst [(y,var z)] M'0)));
      [apply subst_an_aeq_term_is_still_aeq;aeq_solve|]. subst z. 
      apply subst_keep_pr_same_subst_var_aeq_lemma1.
      congruence. solve_notin. solve_notin. apply pr_keep_no_free_occur with (M:=M0);solve_notin. 
    - specialize (H0 M0 M'0 (le_n _) H2 x0 y). destruct H0 as [E1 [? ?]].
      specialize (H1 N N' (le_n _) H3 x0 y). destruct H1 as [E2 [? ?]].
      exists (subst [(x,E2)] E1). split. now constructor. 
      transitivity (subst [(x, E2)] (subst [(x0,var y)] M'0));[aeq_solve|].
      transitivity (subst [(x, subst [(x0,var y)] N')] (subst [(x0, var y)] M'0)).
      apply subst_an_aeq_term_is_still_aeq; aeq_solve. 
      symmetry. apply substitution_lemma. tauto. destruct_eq_dec.
Qed.  

(** If M->>M' , and M=a=N, then exists N', N->>N' and N'=a=M'**)        
Lemma parallel_reduction_preserve_aeq:
  preserve_aeq parallel_reduction.
Proof.
  unfold preserve_aeq. intros. revert N H0. 
  apply pr_rank_induction with (M:=M) (N:=M'); auto; intros.
  + exists N. split;[constructor|aeq_solve].
  + inversion H2;subst. clear H8. rename t2 into N. rename x' into y. 
    symmetry in H2. apply inversion_abs in H2 as ?.
    assert (H5:= H1). apply subst_keep_pr_same_subst_var with (x:=x) (y:=y) in H5.
    destruct H5 as [E [? ?]]. 
    specialize (H0 (subst [(x, var y)] M0) E).
    specialize H0 with (N:=N).
    destruct H0 as [E1 [? ?]];auto. 
    - rewrite <- subst_task_is_var_rank_eq. constructor. repeat constructor. 
    - aeq_solve.
    - exists (abs y E1). split. now constructor.
      transitivity (abs y (subst [(x,var y)] M'0)); [aeq_solve|]. symmetry.
      destruct (var_eq_dec x y). 
      * subst y. apply add_bind_aeq. rewrite subst_var_with_itself. aeq_solve.
      * apply add_different_bind_aeq. easy. apply no_free_occur_if_var_is_substed. destruct_eq_dec.
        symmetry. apply subst_var_and_rollback_aeq.
        assert (free_occur y (abs y N) = 0) by destruct_eq_dec.
        assert (free_occur y (abs x M0) = 0) by aeq_solve.
        apply pr_keep_no_free_occur with (M:= M0). easy. simpl in H9. destruct_eq_dec.  
  + inversion H4;subst.
    specialize (H0 M1 M1' (le_n _) H2 t3 H8). destruct H0 as [_M1 [? ?]].
    specialize (H1 M2 M2' (le_n _) H3 t4 H10). destruct H1 as [_M2 [? ?]].
    exists (app _M1 _M2). split. now constructor. aeq_solve.
  + inversion H4;subst. inversion H8;subst. clear H12.
    rename x' into y.  rename t2 into t0. rename t4 into t1. 
    specialize (H1 N N' (le_n _) H3 t1 H10). destruct H1 as [E2 [? ?]].
    apply subst_keep_pr_same_subst_var with (x:=x) (y:=y) in H2 as ?. 
    destruct H6 as [E1 [? ?]]. symmetry in H8. apply inversion_abs in H8 as ?.
    specialize (H0 (subst [(x,var y)] M0) E1).
    specialize H0 with (N:=t0). 
    destruct H0 as [E3 [? ?]]; aeq_solve.
    { rewrite <- subst_task_is_var_rank_eq. constructor. simpl. repeat constructor. }
    exists (subst [(y,E2)] E3). split. now constructor. 
    transitivity (subst [(y, N')] E3);[apply subst_an_aeq_term_is_still_aeq;aeq_solve|].
    transitivity (subst [(y, N')] (subst [(x, var y)] M'0));[aeq_solve|].
    assert (free_occur y (abs y t0) = 0) by destruct_eq_dec.
    assert (free_occur y (abs x M0) = 0) by aeq_solve.
    destruct (var_eq_dec x y). 
    - subst y. rewrite subst_var_with_itself. aeq_solve.
    - simpl in H14. destruct_eq_dec. assert (free_occur y M'0=0). 
    apply pr_keep_no_free_occur with (M:=M0);tauto. symmetry.
    now apply subst_var_trivial_renaming.
Qed.

Definition alpha_compatible_relation (P:tm->tm->Prop) := forall M N,
(exists M' N', P M' N' /\ M=a= M' /\ N =a= N') -> P M N.

Theorem pr_alpha_induction: forall (P: tm -> tm -> Prop) xs, 
  alpha_compatible_relation P ->
  (forall M, P M M) ->
  (forall x M M', ~ In x xs -> parallel_reduction M M' -> P M M' -> P (abs x M) (abs x M')) ->
  (
    forall M1 M1' M2 M2', 
      parallel_reduction M1 M1' -> P M1 M1' -> 
      parallel_reduction M2 M2' -> P M2 M2' -> 
      P (app M1 M2) (app M1' M2')
  ) ->
  (
    forall x M M' N N', 
      ~ In x xs -> 
      parallel_reduction M M' -> P M M' -> 
      parallel_reduction N N' -> P N N' -> 
      P (app (abs x M) N) (subst [(x, N')] M')
  ) ->
  forall M N, parallel_reduction M N -> P M N.
Proof.
  intros.
  apply H.
  use_variable_convention M xs. 
  pose proof parallel_reduction_preserve_aeq.
  specialize (H7 _ _ _ H4 H5).
  destruct H7 as [E [? ?]].
  exists M0. exists E.
  split;[ | split; aeq_solve].
  clear M N H H4 H5 H8.
  induction H7; intros.
  + auto. 
  + apply H1; auto. apply H6. destruct_eq_dec. apply IHparallel_reduction. 
    intros. apply H6. destruct_eq_dec.
  + apply H2; auto. 
    - apply IHparallel_reduction1. intros. 
      apply H6. destruct_eq_dec. rewrite H. reflexivity.
    - apply IHparallel_reduction2. intros. 
      apply H6. destruct_eq_dec. rewrite H.
      apply orb_true_r.
  + apply H3; auto. apply H6. 
    - destruct_eq_dec.
    - apply IHparallel_reduction1. intros.
      apply H6. destruct_eq_dec. rewrite H. reflexivity.
    - apply IHparallel_reduction2. intros.
      apply H6. destruct_eq_dec. rewrite H. apply orb_true_r.
Qed.

(**  If N->>N', then exists E, M[x|->N] ->> E /\ E'=a= M[x|->N'] **)
Lemma subst_keep_pr_subst_tm_pr: forall x M N N',
  parallel_reduction N N' ->
  exists E, parallel_reduction (subst [(x,N)] M) E /\  E=a= (subst [(x,N')] M).
Proof.
  intros.
  apply alpha_induction with (xs:=x::tm_var N ++ tm_var N') (t:=M); auto; intros.
  + unfold alpha_compatible; intros.
    destruct H1 as [? [? ?]].
    assert (subst [(x,N)] M0 =a= subst [(x,N)] N0) by aeq_solve.
    pose proof (parallel_reduction_preserve_aeq _ _ _ H1 H3).
    destruct H4 as [? [? ?]].
    exists x1. split;[auto|aeq_solve].
  + exists c. simpl. split;[ constructor | aeq_solve] .
  + destruct_eq_dec. 
    - exists N'. split;[ auto |aeq_solve].
    - exists x0. split;[ constructor | aeq_solve] .
  + destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]].
    exists (app x0 x1). split;[ constructor; tauto | simpl; aeq_solve].
  + des_notin H0.
    destruct_eq_dec. 
    assert (free_occur x0 N = 0) by solve_notin.
    assert (free_occur x0 N' = 0) by solve_notin.
    rewrite H4. rewrite H5. simpl. 
    destruct H1 as [? [? ?]].
    exists (abs x0 x1).
    split;[ constructor; tauto | simpl; aeq_solve].
 Qed. 
 
(**  If M->>M', N->>N', then exists E, M[x|->N] ->> E /\ E'=a= M'[x|->N'] **)
Lemma subst_keep_pr: forall x M M' N N',
  parallel_reduction M M' ->
  parallel_reduction N N' ->
  exists E, parallel_reduction (subst [(x,N)] M) E /\ E =a= (subst [(x,N')] M').
Proof.
  intros. apply pr_alpha_induction with (xs:=x::tm_var N ++ tm_var N') (M:=M)(N:=M'); auto; intros.
  + unfold alpha_compatible_relation. intros M0 M1 ?.
    destruct H1 as (M2&M3&(E&?&?)&?&?).
    assert (subst [(x,N)] M2 =a= subst [(x,N)] M0) by aeq_solve.
    pose proof (parallel_reduction_preserve_aeq _ _ _  H1 H5).
    destruct H6 as (?&?&?).
    exists x0. split;[ auto | aeq_solve ].
  + apply subst_keep_pr_subst_tm_pr. tauto.
  + des_notin H1. destruct H3 as (E&?&?).
    simpl. destruct_eq_dec. 
    assert (free_occur x0 N = 0) by solve_notin.
    assert (free_occur x0 N' = 0) by solve_notin.
    rewrite H7. rewrite H8. simpl. 
    exists (abs x0 E).
    split. now constructor. aeq_solve.
  + destruct H2 as [E1[? ?]]. destruct H4 as [E2 [? ?]].
    exists (app E1 E2). split. now constructor. simpl. aeq_solve.  
  + des_notin H1. simpl. destruct_eq_dec.
    assert (free_occur x0 N = 0) by solve_notin.
    assert (free_occur x0 N' = 0) by solve_notin.
    rewrite H8. simpl.
    destruct H3 as [E1[? ?]].
    destruct H5 as [E2[? ?]].
    exists (subst [(x0,E2)] E1).
    split. now constructor.
    transitivity (subst [(x0, E2)] (subst [(x, N')] M'0));[aeq_solve|].
    transitivity (subst [(x0,  subst [(x,N')] N'0)] (subst [(x, N')] M'0));[apply subst_an_aeq_term_is_still_aeq;aeq_solve|].
    symmetry. apply substitution_lemma; tauto.
Qed.

Lemma parallel_reduction_diamond:
  diamond parallel_reduction. 
Proof.   
  unfold diamond.
  intros. generalize dependent M2. apply pr_rank_induction with (M:=M)(N:=M1); auto; intros.
  + exists M2. exists M2. split. auto. split. constructor. aeq_solve. 
  + apply abs_pr_inversion in H2. destruct H2 as [M2' [? ?]]. subst.
    specialize H0 with M0 M' M2'. destruct H0 as (TL&TR&?&?&?); auto.
    exists (abs x TL). exists (abs x TR). split. constructor. tauto. split. constructor. tauto. aeq_solve.
  + apply app_pr_inversion in H4. destruct H4.
    - destruct H4 as [M12' [M22' [? [? ?]]]]. subst.
      specialize H0 with M0 M1' M12'. destruct H0 as (M0L&M0R&?&?&?); auto.
      specialize H1 with M2 M2' M22'. destruct H1 as (M2L&M2R&?&?&?); auto.
      exists (app M0L M2L). exists (app M0R M2R). split. now constructor. 
      split. now constructor. aeq_solve.
    - destruct H4 as [x [P [P' [M2'' [? [? [? ?]]]]]]]. subst.
      apply abs_pr_inversion in H2. destruct H2 as [P'' [? ?]]. subst.
      specialize H0 with P P'' P'. destruct H0 as (PL&PR&?&?&?); auto. simpl. lia.
      specialize H1 with M2 M2' M2''. destruct H1 as (M2L&M2R&?&?&?); auto.
      pose proof subst_keep_pr x P' PR M2'' M2R.
      destruct H10 as (E&?&?); auto.
      exists (subst [(x, M2L)] PL). exists E. 
      split. now constructor. split. tauto. aeq_solve.
      apply subst_an_aeq_term_is_still_aeq; auto.
  + apply app_pr_inversion in H4. destruct H4.
    - destruct H4 as [M'' [N'' [? [? ?]]]]. subst.
      apply abs_pr_inversion in H5.
      destruct H5 as [M''' [? ?]]. subst.
      rename M''' into M''.
      specialize H0 with M0 M' M''. destruct H0 as (M0L&M0R&?&?&?); auto.
      specialize H1 with N N' N''. destruct H1 as (NL&NR&?&?&?); auto.
      pose proof subst_keep_pr x M' M0L N' NL.
      destruct H10 as (E&?&?); auto.
      exists E. exists (subst [(x, NR)] M0R).
      split. tauto. split. now constructor. aeq_solve.
      apply subst_an_aeq_term_is_still_aeq; auto.
    - destruct H4 as [x' [P [P' [M2'' [? [? [? ?]]]]]]]. 
      inversion H4; subst. rename x' into x. clear H4.
      rename P' into P''. rename M2'' into N''.
      rename M' into P'.
      specialize H0 with P P' P''.
      destruct H0 as (PL&PR&?&?&?); auto.
      specialize H1 with N N' N''.
      destruct H1 as (NL&NR&?&?&?); auto.
      pose proof subst_keep_pr x P' PL N' NL. 
      destruct H10 as (E1&?&?); auto. exists E1.
      pose proof subst_keep_pr x P'' PR N'' NR.
      destruct H12 as (E2&?&?); auto. exists E2.
      split. tauto. split. tauto. aeq_solve.
      apply subst_an_aeq_term_is_still_aeq; auto.
Qed.

Lemma rf_beta_parallel_inclusion: 
  inclusion tm (clos_refl tm (clos_comp beta_reduction))  parallel_reduction.
Proof.
    intros x y H. inversion H; subst.
    + clear H. induction H0; subst.
        - inversion H; subst. repeat constructor.
        - constructor. constructor. tauto.
        - constructor. easy. constructor.
        - now constructor.
    + constructor.
Qed.

Lemma bstar_app_l: forall M N Z,
  bstar M N ->
  bstar (app M Z) (app N Z).
Proof.
  cbv. intros. rewrite clos_rt_rtn1_iff in H.
  induction H.
  + reflexivity. 
  + apply cp_app_l with (Z:=Z) in H. etransitivity. apply IHclos_refl_trans_n1. constructor. tauto.
Qed.

Lemma bstar_app_r: forall M N Z,
  bstar M N ->
  bstar (app Z M) (app Z N).
Proof.
  cbv. intros. rewrite clos_rt_rtn1_iff in H.
  induction H.
  + reflexivity. 
  + apply cp_app_r with (Z:=Z) in H. etransitivity. apply IHclos_refl_trans_n1. constructor. tauto.
Qed.

Lemma bstar_abs: forall x M N,
  bstar M N ->
  bstar (abs x M) (abs x N).
Proof.
  cbv. intros. rewrite clos_rt_rtn1_iff in H.
  induction H.
  + reflexivity. 
  + apply cp_abs with (x:=x) in H. etransitivity. apply IHclos_refl_trans_n1. constructor. tauto.
Qed.

Lemma parallel_crt_beta_inclusion:
 inclusion tm parallel_reduction (clos_comp_refl_trans beta_reduction).
Proof.
  unfold clos_comp_refl_trans. intros x y H. induction H.
  + reflexivity.
  + apply bstar_abs. tauto. 
  + transitivity (app M N');[apply bstar_app_r|apply bstar_app_l]; tauto.
  + transitivity (app (abs x M) N'). apply bstar_app_r; tauto. transitivity (app (abs x M') N').
      apply bstar_app_l. apply bstar_abs. tauto. repeat constructor.
Qed.

Lemma rf_then_tr_same_rt: forall {X} (R:relation X), same_relation X (clos_trans X (clos_refl X R)) (clos_refl_trans X R).
Proof.
  cbv. intros. split; intros.
  + induction H;subst.
      - inversion H; subst. constructor. easy. reflexivity.
      - transitivity y; tauto.
  + induction H; subst.
      - repeat constructor. tauto.
      - constructor. constructor 2.
      - constructor 2 with y; tauto.
Qed.

Lemma clos_trans_bound: forall {X} R1 R2 R3, 
  inclusion X R1 R2 ->
  inclusion X R2 R3 ->
  same_relation X (clos_trans X R1) R3 ->
  same_relation X (clos_trans X R2) R3.
Proof.
  unfold inclusion. intros. rewrite same_relation_iff in H1. rewrite same_relation_iff.
  split;intros.
  + induction H2.
      - now apply H0.
      - assert (Transitive R3). intros ? ? ? ? ?. apply H1 in H2. apply H1 in H3. apply H1.
        constructor 2 with (y:=y0) ; tauto. apply H2 with (y:=y); tauto.
  + apply H1 in H2. induction H2.
      - repeat constructor. now apply H.
      - constructor 2 with y; tauto.
Qed.

(**  Beta reduction's transitive closure is parallel reduction's transitive closure. **)
Corollary beta_trans_is_pr_trans:
  same_relation tm (clos_trans tm parallel_reduction) bstar.
Proof.
  eapply clos_trans_bound. 
  + apply rf_beta_parallel_inclusion. 
  + apply parallel_crt_beta_inclusion.
  + apply rf_then_tr_same_rt.
Qed.

Theorem Church_Rosser: 
  CR beta_reduction.
Proof.
 unfold CR.  rewrite <- beta_trans_is_pr_trans. apply trans_diamond.
 + apply parallel_reduction_preserve_aeq.
 + apply parallel_reduction_diamond.
Qed.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  More properties                                              *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Lemma beta_reduction_preserve_aeq: 
  preserve_aeq beta_reduction.
Proof.
  unfold preserve_aeq. intros. induction H. inversion H0; subst. 
  inversion H3; subst. exists (subst [(x',t4)] t2). split. constructor.
  apply aeq_sym in H3. apply inversion_abs in H3 as H6. clear H4 H7.
  apply aeq_free_occur with (x:=x') in H3. simpl in H3. destruct (var_eq_dec x x').
  + subst x'. rewrite subst_var_with_itself in H6. now apply subst_an_aeq_term_is_still_aeq.
  + destruct_eq_dec. transitivity (subst [(x',t4)] (subst [(x, var x')] M)). aeq_solve.
      etransitivity. symmetry. apply (subst_var_trivial_renaming x x' t4 M). congruence.
      now apply subst_an_aeq_term_is_still_aeq.
Qed.

Lemma subst_keep_beta_reduction_same_subst_var: forall x y M M',
  beta_reduction M M' ->
  exists E, beta_reduction (subst [(x, var y)] M)  E /\ E=a=(subst [(x, var y)] M').
Proof.
  intros. induction H.
  simpl. destruct_eq_dec.
  + rewrite subst_nil. eexists. repeat constructor. symmetry. apply subst_one_var_twice_aeq.
  + simpl. eexists. repeat constructor. 
      remember (newvar (y :: tm_var M ++ [x; y]) (varsort y)) as z. rewrite subst_destruct_equal. 2: solve_notin.  
      apply subst_keep_pr_same_subst_var_aeq_lemma1; subst z;  solve_notin. 
   + simpl. eexists. repeat constructor. symmetry. apply substitution_lemma. congruence. destruct_eq_dec. 
Qed.

Lemma beta_reduction_keep_no_free_occur: forall x M N,
  beta_reduction M N ->
  free_occur x M = 0 ->
  free_occur x N = 0.
Proof.
  intros. induction H.
  simpl in H0. destruct_eq_dec.
  + now apply no_free_occur_if_var_is_substed.
  + zero_r H0. now apply subst_one_term_keep_no_free_occur. 
Qed.

Corollary clos_comp_beta_reduction_keep_no_free_occur: forall x M N,
  clos_comp beta_reduction M N ->
  free_occur x M = 0 ->
  free_occur x N = 0.
Proof.
  intros. induction H.
  + now apply beta_reduction_keep_no_free_occur with (M:=M).
  + zero_r H0. simpl. rewrite H0. now rewrite IHclos_comp.
  + zero_r H0. simpl. rewrite H1. now rewrite IHclos_comp.
  + simpl in H0. simpl. destruct_eq_dec.
Qed.

Corollary bstar_keep_no_free_occur: forall x M N,
  bstar M N ->
  free_occur x M = 0 ->
  free_occur x N = 0.
Proof.
  intros. induction H.
  + eapply clos_comp_beta_reduction_keep_no_free_occur; eauto.
  + easy.
  + tauto.
Qed.

(** If M->β M', then exists E, M[x|->y] ->β E /\ E=a=M'[x|->y] **)
Lemma subst_keep_clos_comp_beta_reduction_same_subst_var: forall x y M M',
  clos_comp beta_reduction M M' ->
  exists E, clos_comp beta_reduction (subst [(x, var y)] M)  E /\ E=a=(subst [(x, var y)] M').
Proof.
  intros. revert x y M' H. induction M using rank_induction. 
  destruct M; intros; inversion H0; subst; simpl.
  + inversion H1. 
  + inversion H1.
  + pose proof subst_keep_beta_reduction_same_subst_var x y (app M1 M2) M'.
      destruct H2; try easy. exists x0. split. now constructor. easy.
  + specialize H with M2 x y N. destruct H. apply lt_app_rank_r. easy. 
      exists (app (subst [(x, var y)] M1) x0). split. now constructor 2. aeq_solve.
  + specialize H with M1 x y N. destruct H. apply lt_app_rank_l. easy. 
      exists (app x0 (subst [(x, var y)] M2) ). split. now constructor 3. aeq_solve.
  + inversion H1. 
  + destruct_eq_dec.
      - repeat rewrite subst_nil. specialize H with M x x N.
        destruct H; try easy. constructor. 
        repeat rewrite subst_var_with_itself in H.
        exists (abs x x0). split. now constructor 4. aeq_solve.
      - simpl. repeat rewrite subst_destruct_equal. 2: solve_notin.
         2: solve_notin.  
         remember ( newvar (y :: tm_var M ++ [x; y]) (varsort y)) as z1.
         remember ( newvar (y :: tm_var N ++ [x; y]) (varsort y)) as z2.
         assert (H1:=H). specialize H1 with M y z1 N.
         destruct H1 as [N' [? ?]]. constructor. easy.
         specialize H with (subst [(y,var z1)] M) x y N'. 
         destruct H as [N'' [? ?] ]. 
         rewrite <- subst_task_is_var_rank_eq; try now repeat constructor.
         easy. exists (abs z1 N''). split. now constructor 4.
         destruct (var_eq_dec z1 z2).
         * rewrite <- e. aeq_solve.
         * apply add_different_bind_aeq. subst. now repeat rewrite newvar_sort. 
            apply subst_one_term_keep_no_free_occur. 2: solve_notin. 
            apply subst_one_term_keep_no_free_occur. 2:solve_notin.
            assert (free_occur z1 M = 0) by solve_notin.
            now apply clos_comp_beta_reduction_keep_no_free_occur with (M:=M).
            transitivity (subst [(x,var y)] (subst [(y, var z1)] N)). aeq_solve.
            apply subst_keep_pr_same_subst_var_aeq_lemma2; subst;[ solve_notin.. | |solve_notin] .
            apply clos_comp_beta_reduction_keep_no_free_occur with (M:=M). easy. solve_notin.
        - simpl. specialize H with M x y N. destruct H; try easy. constructor.
           exists (abs v x0). split. now constructor 4. aeq_solve.
Qed.

(** If M->β M' , and M=a=N, then exists N', N->β N' and N'=a=M'**)        
Corollary clos_comp_beta_reduction_preserve_aeq: 
  preserve_aeq (clos_comp beta_reduction).
Proof.
  unfold preserve_aeq. intros. revert M' N  H H0. induction M using rank_induction.
  destruct M; intros.
  + inversion H1; subst. inversion H0; subst. inversion H2; subst.
  + inversion H1; subst. inversion H0; subst. inversion H2; subst. inversion H0; subst. inversion H2; subst.
  + inversion H0; subst.
      - pose proof beta_reduction_preserve_aeq (app M1 M2) M' N. destruct H3; try easy.
        exists x. split. now constructor. easy.
      - inversion H1; subst. specialize H with M2 N0 t4. destruct H; try easy.
        apply lt_app_rank_r. exists (app t3 x). split. now constructor 2. aeq_solve.
      - inversion H1; subst. specialize H with M1 N0 t3. destruct H; try easy.
        apply lt_app_rank_l. exists (app x t4). split. now constructor 3. aeq_solve.
  + inversion H0; subst.
      - inversion H2; subst.
      - inversion H1; subst.  clear H8. rename t2 into M'. rename x' into s'. 
        assert (H100:=H1). apply aeq_sym in H1. apply inversion_abs in H1.  
        pose proof subst_keep_clos_comp_beta_reduction_same_subst_var v s' M N0.
        destruct H2. easy. specialize H with (subst [(v, var s')] M) x M'.
        destruct H. rewrite <- subst_task_is_var_rank_eq; now repeat constructor.
        easy. aeq_solve. exists (abs s' x0). split. now constructor 4.
        destruct (var_eq_dec s' v).
        * subst. repeat rewrite subst_var_with_itself in H2. aeq_solve. transitivity x; aeq_solve. 
        * apply add_different_bind_aeq. easy. 
           apply clos_comp_beta_reduction_keep_no_free_occur with (M:=M).
           easy. apply aeq_free_occur with (x:=s') in H100. simpl in H100. destruct_eq_dec. 
           transitivity x; aeq_solve.
Qed.

(**  If M->β* M', N->>N', then exists E, M[x|->N] ->β* E /\ E'=a= M'[x|->N'] **)
Corollary bstar_preserve_aeq: 
  preserve_aeq bstar.
Proof.
  unfold preserve_aeq. intros. revert N H0. induction H; intros.
  + pose proof clos_comp_beta_reduction_preserve_aeq x y N. destruct H1; try easy.
      exists x0. split. constructor. easy. easy.
  + exists N. split. constructor 2. aeq_solve.
  + specialize IHclos_refl_trans1 with N. destruct IHclos_refl_trans1. easy. destruct H2.
      specialize IHclos_refl_trans2 with x0. destruct IHclos_refl_trans2. aeq_solve.
      destruct H4. exists x1. split. now constructor 3 with x0. easy.
Qed.

(** Beta-normal form: Can not be beta reduced **)
Definition beta_normal_form (t:tm):=
  ~ (exists t', clos_comp beta_reduction t t').
  
Lemma str_bnf: forall s,
  beta_normal_form (var s).
Proof. cbv. intros. destruct H. inversion H; subst. inversion H0. Qed.

Lemma cons_bnf: forall c,
  beta_normal_form (cons c).
Proof. cbv. intros. destruct H. inversion H; subst. inversion H0. Qed.

Lemma app_bnf: forall t1 t2,
   beta_normal_form (app t1 t2) -> (beta_normal_form t1 /\ beta_normal_form t2).
Proof.
  unfold beta_normal_form. unfold not. split; intros.
  + apply H. destruct H0. exists (app x t2). now constructor. 
  + apply H. destruct H0. exists (app t1 x). now constructor.
Qed. 

Inductive not_abs: tm -> Prop:= 
  | str_not_abs: forall s, not_abs (var s)
  | cons_not_abs: forall c, not_abs (cons c)
  | app_not_abs: forall t1 t2, not_abs (app t1 t2).
  
Lemma app_bnf_not_abs: forall t1 t2,
  beta_normal_form t1 ->
  beta_normal_form t2 ->
  not_abs t1 ->
  beta_normal_form (app t1 t2).
Proof.
  cbv. intros. destruct H2. inversion H2; subst.
  + inversion H3; subst. inversion H1.
  + apply H0. eauto.
  + apply H. eauto.
Qed. 
 
Lemma abs_bnf: forall x t,
  beta_normal_form (abs x t) <-> beta_normal_form t.
Proof.
  cbv. split; intros.
  + destruct H0. apply H. exists (abs x x0). now constructor 4.
  + destruct H0. inversion H0; subst.
      - inversion H1.
      - apply H. eauto.
Qed. 

  
Lemma bnf_reduction_is_self: forall t t',
  beta_normal_form t ->
  bstar t t' ->
  t = t'.
Proof.
  cbv. intros. revert H.
  induction H0; intros.
  + exfalso. apply H0. eauto.
  + easy.
  + assert (x=y). apply IHclos_refl_trans1. easy. 
     subst y. apply IHclos_refl_trans2. easy.
Qed.

(**  By Church Rosser, if a term can be beta-reduced to two normal forms, then they are alpha-quaivalent **)
Corollary two_bnf_aeq: forall M M1 M2,
  bstar M M1 ->
  bstar M M2 ->
  beta_normal_form M1 ->
  beta_normal_form M2 ->
  aeq M1 M2.
Proof.
  intros. pose proof (Church_Rosser M M1 M2 H H0).
  destruct H3 as [M3 [M4 [? [? ?]]]].
  apply bnf_reduction_is_self in H3.
  apply bnf_reduction_is_self in H4.
  congruence. easy. easy.
Qed.

(** If one normal form is alpha-equivalent to the other, then the other one is also in normal form**)
Corollary aeq_bnf_then_bnf: forall M N,
  aeq M N ->
  beta_normal_form M ->
  beta_normal_form N.
Proof.  
  unfold beta_normal_form. intros. unfold not.
  intros. destruct H1. pose proof clos_comp_beta_reduction_preserve_aeq N x M.
  destruct H2; try easy. assert (exists t', clos_comp beta_reduction M t').
  exists x0. easy. contradiction. 
Qed.


Ltac check_bnf:=
  repeat match goal with
  | |- beta_normal_form (cons _) => apply cons_bnf
  | |- beta_normal_form (var _) => apply str_bnf
  | |- beta_normal_form (app _ _) => apply app_bnf_not_abs
  | |- beta_normal_form (abs _ _) => apply abs_bnf
  | |- not_abs _ => constructor
  end.
  
Lemma bstar_app : forall M N M' N',
  bstar M M' ->
  bstar N N' ->
  bstar (app M N) (app M' N').
Proof.
  intros. constructor 3 with (app M' N).
  + now apply bstar_app_l.
  + now apply bstar_app_r.
Qed.

Ltac check_bstar:= 
  repeat ( unfold bstar; unfold clos_comp_refl_trans; match goal with   
  | |- clos_refl_trans tm (clos_comp beta_reduction) ?t ?t => apply rt_refl
  | |- clos_refl_trans tm (clos_comp beta_reduction) (abs ?s _) (abs ?s _) => apply bstar_abs
  | |- clos_refl_trans tm (clos_comp beta_reduction) (app ?M _) (app ?M _) => apply bstar_app_r
  | |- clos_refl_trans tm (clos_comp beta_reduction) (app _ ?N) (app _ ?N) => apply bstar_app_l
  | |- clos_refl_trans tm (clos_comp beta_reduction) (app _ _) (app _ _) => apply bstar_app
  end ); fold clos_comp_refl_trans; fold bstar; try tauto.
  
End General_lambda.