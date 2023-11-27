Require Import Coq.Lists.List.
Require Import Permutation.
Import ListNotations.

(***** DeMorgan *****)
Theorem deMorgan1 (A B: Prop): ~(A\/B) -> ~A/\~B.
Proof.
  intro NAB.
  split.

  (* NAB: ~(A\/B) |- ~A *)
  - intro A1.
    apply NAB.
    left.
    exact A1.

  (* NAB ~(A\/B) |- ~B *)
  - intro B1.
    apply NAB.
    right.
    exact B1.
Qed.

Theorem deMorgan2 (A B: Prop): ~A/\~B -> ~(A\/B).
Proof.
  intros NANB AB.
  destruct NANB as [NA NB].
  destruct AB as [A1 | B1].

  (* NA:~A, NB:~B A1:A |- False *)
  - apply NA.
    exact A1.

  (* NA:~A, NB:~B B1:B |- False *)
  - apply NB.
    exact B1.
Qed.

(***** Lemmas about app *****)
Lemma app_nil: forall {A:Type} (l1 l2: list A),
  l1 = [] /\ l2 = [] <-> (l1++l2) = [].
Proof.
  split.
  + intros. destruct H.  rewrite H. rewrite H0. reflexivity.
  + apply app_eq_nil.
Qed.

Lemma app_injection_length_l: forall {A:Type} (l1 l2 l3 l4: list A),
  l1 ++ l2 = l3 ++ l4 ->
  length l1 = length l3 ->
  l1 = l3 /\ l2 = l4.
Proof.
  intros. revert l2 l3 l4 H H0. induction l1;intros.
  + simpl in H. destruct l3. simpl in H. tauto. inversion H0.
  + destruct l3. inversion H0.
    inversion H;subst. specialize IHl1 with l2 l3 l4.
    apply IHl1 in H3; try tauto. destruct H3. split;congruence.    
    simpl in H0. injection H0. tauto.
Qed.

Lemma app_injection_length_r: forall {A:Type} (l1 l2 l3 l4: list A),
  l1 ++ l2 = l3 ++ l4 ->
  length l2 = length l4 ->
  l1 = l3 /\ l2 = l4.
Proof.
  intros. assert (length (l1++l2) = length (l3 ++ l4)).
  rewrite H. reflexivity.  repeat rewrite app_length in H1.
  rewrite H0 in H1. rewrite PeanoNat.Nat.add_cancel_r in H1.
  apply app_injection_length_l; tauto.
Qed.

Lemma not_in_app: forall {A:Type} (x:A) l1 l2,
  ~ In x (l1++l2) <-> ~In x l1 /\ ~ In x l2.
Proof.
  intros. split;intros. 
  + induction l1.
    - simpl. simpl in H. tauto.
    - split.
      * apply not_in_cons. simpl in H. apply deMorgan1 in H. split.
        destruct H. congruence. tauto.
      * simpl in H. apply deMorgan1 in H. tauto.
  + induction l1. simpl. tauto.
    destruct H. apply not_in_cons in H. assert (~ In x l1 /\ ~ In x l2). tauto.
    apply IHl1 in H1. simpl. apply deMorgan2. split;[destruct H;congruence|tauto]. 
Qed.

Lemma not_in_forall: forall {A:Type}(x:A) l,
  ~ In x l <-> Forall (fun s => x <> s) l.
Proof.
  split; intros.
  + apply Forall_forall. intros. induction l. inversion H0.
      apply not_in_cons in H. destruct H. destruct H0. congruence. tauto.
  + rewrite Forall_forall in H. induction l. easy.
      apply not_in_cons. split. apply (H a). left. congruence. apply IHl. intros.
      apply H. right. easy.
Qed.
 

(***** Lemmas about zero_sum *****)
Lemma zero_sum_r: forall a b:nat,
a+b=0 -> a=0 /\ b=0.
Proof.
  apply Plus.plus_is_O.
Qed. 

Lemma zero_sum_l: forall a b:nat,
0=a+b -> a=0 /\ b=0.
Proof.
  intros. symmetry in H. apply zero_sum_r. exact H.
Qed. 

Local Ltac zero_r1 H:=
  let H0:= fresh "H" in
  match type of  H with
  | _ + _ = 0 => apply zero_sum_r in H; destruct H as [H H0]; try rewrite H0; zero_r1 H
  | _ => try rewrite H
  end.
  
Ltac zero_r H:= simpl in H; 
              zero_r1 H; match goal with
             | |- context [ 0 + _ ] => simpl plus
             | |- context [ _ + 0 ] => rewrite plus_n_O
             | |- _ => idtac
              end; try congruence; try tauto.

Local Ltac zero_l1 H:=
  let H0:= fresh "H" in
  match type of  H with
  | 0 = _ + _ => apply zero_sum_l in H; destruct H as [H H0]; try rewrite H0; zero_l1 H
  | _ => try rewrite H
  end.
  
Ltac zero_l H:= simpl in H; zero_l1 H; match goal with
             | |- context [ 0 + _ ] => simpl plus
             | |- context [ _ + 0 ] => rewrite plus_n_O
             | |- _ => idtac
              end;try congruence; try tauto.

Lemma Forall_cons_iff: forall {A:Type}(P:A->Prop)(x:A)(l:list A),
  P x /\ Forall P l <-> Forall P (x::l).
Proof. 
  split;intros.
  + apply Forall_cons;tauto.
  + split;revert H;[apply Forall_inv|apply Forall_inv_tail].
Qed.

Ltac forall_cons H:=
  let H0:= fresh "H" in
  match type of H with
  | Forall _ (cons _ _) => rewrite <- Forall_cons_iff in H; destruct H as [H H0]
  end.
  
Ltac des_notin H:=  
  let  H0:= fresh "H" in
  simpl in H; match type of H with
  | ~ In _ (cons _ _) => apply deMorgan1 in H; destruct H as [H H0];  try des_notin H0
  | ~ In _ (_ ++ _) => rewrite not_in_app in H; destruct H as [H H0]; try des_notin H ; try des_notin H0
  | ~ ( _ \/ _ ) => apply deMorgan1 in H; destruct H as [H H0]; try des_notin H ; try des_notin H0
  | _ => idtac
  end.
  
Lemma some_injective: forall A (x y:A),
  Some x = Some y -> x=y.
Proof.  intros. now injection H. Qed.

Ltac add_some:= try apply some_injective.

Section length_induction.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem length_induction: forall xs, P xs.
  Proof.
    assert (forall xs n, length xs < n -> P xs) as H_ind.
    { intros. generalize dependent xs. induction n; intros.
        + inversion H0.
        + apply H. intros. apply IHn.  apply Lt.lt_n_Sm_le in H0.
        inversion H0;subst. tauto.
        now apply PeanoNat.Nat.lt_le_trans with (length xs). }
    intros. apply H_ind with (S (length xs)). constructor.
Qed.

Inductive nat_reflect (P:Prop): nat -> Prop:=
 | ReflectS (H:P): nat_reflect P 1
 | ReflectO (H:~P): nat_reflect P 0.

End length_induction.

Lemma Permutation_app_comm_with_cons: forall (A:Type) (x y: A)(l1 l2:list A),
  Permutation (x::l1 ++ y::l2) (y::l2++x::l1).
Proof. intros.  pose proof Permutation_app_comm (x::l1) (y::l2). now simpl in H. Qed. 

Lemma Permutation_app_comm_with_cons_tail: forall (A:Type) (x y: A)(l1 l2 l3 l4:list A),
  Permutation l3 l4 ->
  Permutation (x::l1 ++ y::l2++l3) (y::l2++x::l1++l4).
Proof. 
    intros.  pose proof Permutation_app_comm_with_cons A x y l1 l2.
    pose proof Permutation_app H0 H.   repeat rewrite <- app_comm_cons in H1.
    repeat rewrite <- app_assoc in H1.  repeat rewrite <- app_comm_cons in H1.
    now simpl in H. 
Qed. 

Lemma Permutation_app_rot_tail: forall A (l1 l2 l3 l4 l5: list A),
  Permutation l4 l5 ->
  Permutation (l1++l2++l3++l4) (l2++l3++l1++l5).
Proof. 
  intros. pose proof Permutation_app_rot l1 l2 l3. pose proof Permutation_app H0 H. 
  now repeat rewrite <- app_assoc in H1.
Qed.

Lemma Permutation_app_swap_app_tail: forall A (l1 l2 l3 l4 l5:list A),
  Permutation l4 l5 ->
  Permutation (l1++l2++l3++l4) (l2++l1++l3++l5).
Proof.
   intros. pose proof Permutation_app_swap_app l1 l2 l3. pose proof Permutation_app H0 H. 
   now repeat rewrite <- app_assoc in H1.
Qed.

Lemma Permutation_app_comm_tail: forall A (l1 l2 l3 l4:list A),
  Permutation l3 l4 ->
  Permutation (l1++l2++l3) (l2++l1++l4).
Proof.
   intros. pose proof Permutation_app_comm l1 l2. pose proof Permutation_app H0 H. 
   now repeat rewrite <- app_assoc in H1.
Qed.

Lemma Permutation_middle_tail: forall A (x:A) (l1 l2 l3 l4:list A),
  Permutation l3 l4 ->
  Permutation (x::l1++l2++l3) (l1++x::l2++l4).
Proof.
   intros. pose proof Permutation_middle l1 l2 x. pose proof Permutation_app H0 H. 
    repeat rewrite <- app_comm_cons in H1. now repeat rewrite <- app_assoc in H1.
Qed.  
 
Ltac perm:=
  repeat match goal with
  | |- Permutation ?t ?t => apply Permutation_refl
  | H: Permutation ?a ?b |- Permutation ?a ?b => apply H
  | |- Permutation (_++?a) (_++?a) => apply Permutation_app_tail
  | |- Permutation (?x::_) (?x::_) => constructor
  | |- Permutation (?x::?y::_) (?y::?x::_) => constructor
  | |- Permutation (?a++ _ )(?a++_) => apply Permutation_app_head
  | |- Permutation (?a++?b++?c) (?b++?c++?a) => apply Permutation_app_rot
  | |- Permutation (?a++?b++?c++_) (?b++?c++?a++_) => apply Permutation_app_rot_tail
  | |- Permutation (?a++?b++?c) (?b++?a++?c) => apply Permutation_app_swap_app
  | |- Permutation (?a++?b++?c++_) (?b++?a++?c++_) => apply Permutation_app_swap_app_tail
  | |- Permutation (?a++?b) (?b++?a) => apply Permutation_app_comm
  | |- Permutation (?a++?b++_) (?b++?a++_) => apply Permutation_app_comm_tail
  | |- Permutation (?x::?a++?b) (?a++?x::?b) => apply Permutation_middle
  | |- Permutation (?x::?a++?b++_) (?a++?x::?b++_) => apply Permutation_middle_tail
  | |- Permutation (?x::?a++?y::?b)(?y::?b++?x::?a) => apply Permutation_app_comm_with_cons
  | |- Permutation (?x::?a++?y::?b++_)(?y::?b++?x::?a++_) => apply Permutation_app_comm_with_cons_tail
  | H: Permutation ?a ?b |- Permutation ?b ?a => now apply Permutation_sym
  | H: Permutation ?a ?b |- Permutation ?a ?c => apply Permutation_trans with b;[exact H| clear H]
  | H: Permutation ?a ?b |- Permutation ?c ?a => apply Permutation_trans with b;[clear H|now apply Permutation_sym]
  | H: Permutation ?b ?a |- Permutation ?a ?c => apply Permutation_trans with b;[now apply Permutation_sym| clear H]
  | H: Permutation ?b ?a |- Permutation ?c ?a => apply Permutation_trans with b;[clear H|exact H]
  | |- Permutation (map ?f _) (map ?f _) => apply Permutation_map
  | _ => tauto
  end.