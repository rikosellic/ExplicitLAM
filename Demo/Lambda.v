Require Import FV.lambda_binding.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Require Import FV.Demo.Naming.

Import ListNotations.


Module LambdaNaming <:lambda_binding.Naming_module_type.
Export Naming.
 

Definition C:=identifier.
Definition V:=ustr.
Definition VS:=ustr_Type.


Lemma constant_eq_dec: forall (x y:C), {x=y}+{x<>y}.
Proof. apply identifier_eq_dec. Qed.

Lemma var_eq_dec: forall (x y: V), {x=y}+{x<>y}.
Proof. apply uvar_eq_dec. Qed.

 
Definition newvar :list V ->  VS -> V:= new_ustr.
  
Definition varsort: V -> VS := check_ustr_type.

Lemma newvar_sort: forall xs T, varsort (newvar xs T) = T.
Proof. apply new_ustr_type. Qed.


Lemma newvar_fresh:  forall (xs:list V) (T:VS), ~ In (newvar xs T) xs.
Proof. apply new_ustr_valid. Qed.

Lemma newvar_Permutation:forall (l1 l2:list V)(T:VS), Permutation l1 l2 -> newvar l1 T = newvar l2 T.
Proof. apply new_ustr_Permutation.  Qed. 
 
End LambdaNaming.

Module LAM:= General_lambda LambdaNaming.