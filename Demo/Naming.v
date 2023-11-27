Require Import FV.ExplicitName.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import FV.utils.
Import ListNotations.

Module Naming.

Module V:=StringName.
Module R:=StringName.

Inductive identifier:Set:=
| iempty
| isingleton
| iunion
| iintersection
| iPEq
| iPRel
| iPTrue
| iPFalse
| iPNot
| iPAnd
| iPOr
| iPIff
| iPImpl
| iPForall
| iPExists
.

Inductive ustr:Type:=
| uvar (v:V.t)
| upred (r:R.t)
.

Coercion uvar: V.t >-> ustr.

Inductive ustr_Type:Type:=
| variable
| predname
.

Lemma in_vars_dec: forall (x:V.t) xs, {In x xs}+{~ In x xs}.
Proof. apply (In_dec V.eq_dec). Qed.

Lemma in_preds_dec: forall (x:R.t) xs, {In x xs}+{~ In x xs}.
Proof. apply (In_dec R.eq_dec). Qed.

Lemma identifier_eq_dec: forall (x y: identifier), {x=y}+{x<>y}.
Proof. intros x y; destruct x; destruct y;try auto;right;congruence. Qed.


Lemma uvar_eq_dec: forall (x y: ustr), {x=y}+{x<>y}.
Proof.
  intros; destruct x; destruct y.
  + destruct (V.eq_dec v v0); [left | right]; congruence.
  + right. congruence.
  + right. congruence.
  + destruct (R.eq_dec r r0);[left | right]; congruence.
Qed.

Definition ustr_occur (x y: ustr):=
  match x, y with
  | uvar x1, uvar y1 => if V.eq_dec x1 y1 then S O else O
  | upred x1, upred y1 => if R.eq_dec x1 y1 then S O else O
  | _ , _ => O
  end.
  
Lemma ustr_occur_eq_dec: forall x y,
  ustr_occur x y = 1 <-> x = y.
Proof.
  split; intros.
  + destruct x; destruct y; try discriminate H.
      - simpl in H. destruct (V.eq_dec v v0). subst. easy. discriminate.
      - simpl in H. destruct (R.eq_dec r r0). subst. easy. discriminate.
  + destruct x; destruct y; try discriminate H.
      - simpl. destruct (V.eq_dec v v0); congruence.
      - simpl. destruct (R.eq_dec r r0); congruence. 
Qed.

Lemma ustr_occur_not_eq_dec: forall x y,
  ustr_occur x y = 0 <-> x <> y.
Proof.
  split; intros.
  + destruct x; destruct y; try discriminate H; try congruence.
      - simpl in H. destruct (V.eq_dec v v0). discriminate. congruence.
      - simpl in H. destruct (R.eq_dec r r0). discriminate. congruence. 
  + destruct x; destruct y; try easy. 
      - simpl. destruct (V.eq_dec v v0); congruence.
      - simpl. destruct (R.eq_dec r r0); congruence.
Qed.
 
Lemma ustr_occur_eq: forall x y,
  nat_reflect (x=y) (ustr_occur x y).
Proof.
  intros. destruct (uvar_eq_dec x y). 
  + apply ustr_occur_eq_dec in e as H. rewrite H. now constructor.
  + apply ustr_occur_not_eq_dec in n as H. rewrite H. now constructor.
Qed.

Fixpoint variable_list (xs:list ustr): list V.t:=
  match xs with
  | nil => nil
  | s::xs0 => match s with
                    | uvar x => x::(variable_list xs0)
                    | _ => variable_list xs0
                    end
  end.
  
Fixpoint predname_list (xs:list ustr): list R.t:=
  match xs with
  | nil => nil
  | s::xs0 => match s with
                    | upred r => r::(predname_list xs0)
                    | _ => predname_list xs0
                    end
  end.
 
Definition new_ustr (xs:list ustr)(T:ustr_Type):ustr:=
  match T with
  | variable => uvar (V.list_new_name (variable_list xs))
  | predname => upred (R.list_new_name (predname_list xs))
  end.
  
Definition check_ustr_type (x:ustr):=
  match x with
  | uvar _ => variable
  | upred _ => predname
  end.

Lemma new_ustr_type: forall xs T, check_ustr_type (new_ustr xs T) = T.
Proof.
  intros. destruct T; reflexivity.
Qed.

Lemma variable_list_app: forall l1 l2,
  variable_list (l1++l2) = variable_list l1 ++ variable_list l2.
Proof.
  intros. induction l1. easy.  
  destruct a; simpl; [f_equal|]; easy.
Qed.

Lemma predname_list_app: forall l1 l2,
  predname_list (l1++l2) = predname_list l1 ++ predname_list l2.
Proof.
  intros. induction l1. easy.  
  destruct a; simpl; [|f_equal]; easy.
Qed.

Lemma str_list_split_by_type: forall (x:ustr) xs,
  In x xs -> (exists v, x=uvar v /\ In v (variable_list xs)) \/ (exists r, x=upred r /\ In r (predname_list xs)).
Proof.
  intros. induction xs.
  + inversion H.
  + destruct H.
      - subst a. destruct x.
        * left. exists v. split;[easy| left; reflexivity].
        * right. exists r.  split;[easy| left; reflexivity].
      - apply IHxs in H. clear IHxs. destruct H;destruct H; destruct H.
        * subst x. left. exists x0. split. easy. simpl. destruct a;[right|];easy.
        * subst x. right. exists x0. split. easy. simpl. destruct a;[|right];easy.
Qed.

Lemma new_ustr_valid:  forall (xs:list ustr) (T:ustr_Type), ~ In (new_ustr xs T) xs.
 Proof.
    intros. rewrite not_in_forall. rewrite Forall_forall. intros.
    apply str_list_split_by_type in H.  destruct H; destruct H;destruct H; subst x.
    + destruct T; simpl.
        - apply V.list_new_name_new in H0. congruence.
        - congruence.
    + destruct T; simpl.
        - congruence.
        - apply R.list_new_name_new in H0. congruence.
Qed.
 
Lemma variable_list_Permutation: forall l1 l2,
  Permutation l1 l2 -> Permutation (variable_list l1) (variable_list l2).
Proof.
  intros. induction H.
  + constructor.
  + destruct x.
      - simpl. now constructor.
      - now simpl.
  + destruct x; destruct y; simpl; try now constructor. apply Permutation_refl.
  + etransitivity. apply IHPermutation1. easy.
Qed.

Lemma variable_list_map_uvar: forall xs,
  variable_list (map uvar xs) = xs.
Proof. induction xs. easy. simpl. congruence. Qed.
  

Lemma predname_list_Permutation: forall l1 l2,
  Permutation l1 l2 -> Permutation (predname_list l1) (predname_list l2).
Proof.
  intros. induction H.
  + constructor.
  + destruct x.
      - now simpl. 
      - simpl. now constructor.
  + destruct x; destruct y; simpl; try now constructor. apply Permutation_refl.
  + etransitivity. apply IHPermutation1. easy.
Qed.
         

Lemma new_ustr_Permutation:forall (l1 l2:list ustr)(T:ustr_Type), Permutation l1 l2 -> new_ustr l1 T = new_ustr l2 T.
 Proof.  
  intros. destruct T; simpl; f_equal.
  + apply V.list_new_name_Permutation. now apply variable_list_Permutation.
  + apply R.list_new_name_Permutation. now apply predname_list_Permutation.
Qed. 

Definition _x := V.default.
Definition _y := V.next_name _x.
Definition _z := V.next_name _y.
Definition _u := V.next_name _z.
Definition _v := V.next_name _u.
Definition _w := V.next_name _v.
Definition _a := V.next_name _w.
Definition _b := V.next_name _a.
Definition _c := V.next_name _b.
Definition _d := V.next_name _c.
Definition _e := V.next_name _d.
Definition _f := V.next_name _e.
Definition _g := V.next_name _f.

End Naming.