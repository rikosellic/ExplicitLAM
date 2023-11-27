Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import FV.Demo.Naming.
Require Import FV.utils.
Import ListNotations.


Module DemoSugarFOL.
Export Naming.

Inductive term := 
| var (v:V.t)
| empty_set
| singleton (x:term)
| union (x y: term) 
| intersection (x y:term).

Inductive atom:=
| APred (r:R.t)
| AApp (a:atom)(t:term).

Inductive prop: Type :=
| PEq (t1 t2: term): prop
| PRel (t1 t2: term): prop
| PAtom (a:atom): prop
| PFalse: prop
| PTrue: prop
| PNot(P: prop)
| PAnd (P Q: prop): prop
| POr(P Q: prop): prop
| PImpl (P Q: prop): prop
| PIff (P Q: prop): prop
| PForall (x: V.t) (P: prop): prop
| PExists (x: V.t)(P:prop): prop
| PPredDef (r:R.t)(xs:list V.t)(P:prop)(Q:prop)
.

Declare Custom Entry sset.

Coercion var: V.t >-> term.

Declare Scope Sugar_scope.
Bind Scope Sugar_scope with term.
Bind Scope Sugar_scope with prop.
Delimit Scope Sugar_scope with s.

Notation "[[ e ]]" := e (at level 2, e custom sset at level 99): Sugar_scope.
Notation "( x )" := x (in custom sset, x custom sset at level 99): Sugar_scope.
Notation "x" := x (in custom sset at level 0, x constr at level 0): Sugar_scope.
Notation "∅":= empty_set (in custom sset at level 5, no associativity): Sugar_scope.
Notation "{ x }":= (singleton x) (in custom sset at level 5, x at level 13, no associativity): Sugar_scope.
Notation "x ∩ y" := (intersection x y)(in custom sset at level 11, left associativity): Sugar_scope.
Notation "x ∪  y" := (union x y)(in custom sset at level 12, left associativity): Sugar_scope.
Notation "x = y" := (PEq x y) (in custom sset at level 20, no associativity): Sugar_scope.
Notation "x ∈ y" := (PRel x y) (in custom sset at level 20, no associativity): Sugar_scope.
(* Notation " '<' a '>'":= (PAtom a)(in custom sset at level 22, no associativity): Sugar_scope. *)
Notation "¬ P" := (PNot P) (in custom sset at level 23, right associativity): Sugar_scope.
Notation "P1 /\ P2" := (PAnd P1 P2) (in custom sset at level 24, left associativity): Sugar_scope.
Notation "P1 \/ P2" := (POr P1 P2) (in custom sset at level 26, left associativity): Sugar_scope.
Notation "P1 -> P2" := (PImpl P1 P2) (in custom sset at level 27, right associativity): Sugar_scope.
Notation "P1 <-> P2" := (PIff P1 P2) (in custom sset at level 28, no associativity): Sugar_scope.
Notation "∃ x , P" := (PExists x P) (in custom sset at level 29,  right associativity): Sugar_scope.
Notation "∀ x , P" := (PForall x P) (in custom sset at level 29, right associativity): Sugar_scope.
Notation " 'var2tm' x":= (var x) (in custom sset at level 5, only parsing, x constr): Sugar_scope.
Notation " 'let' r xs ':=' P 'in' Q":= (PPredDef r xs P Q) (in custom sset at level 30, no associativity): Sugar_scope.
(* Notation " r t1 .. tn " :=
  (AApp ( .. (AApp (APred r) t1) .. ) tn) (in custom sset at level 21, only printing,  no associativity): Sugar_scope. *)

  
Open Scope Sugar_scope.

Definition var_occur (x: V.t) (y: V.t):nat:=
  if V.eq_dec x y then (S O) else O.
  
Definition pred_pred_occur (x: R.t) (y: R.t):nat:=
  if R.eq_dec x y then (S O) else O.

Fixpoint term_occur (x: V.t) (t: term): nat :=
    match t with
    | [[∅]] => O
    | var x0 => if V.eq_dec x x0 then S O else O
    | [[{x0}]] => term_occur x x0
    | [[ x0 ∩ y0 ]]
    | [[ x0 ∪ y0 ]] => term_occur x x0 + term_occur x y0
    end.
  
Fixpoint atom_occur (x:V.t) (a: atom): nat:=
  match a with
  | APred r => O
  | AApp a0 t => atom_occur x a0 + term_occur x t
  end.
  
Fixpoint in_vars (x:V.t) (xs:list V.t) := 
  match xs with
  | nil => false
  | s::xs0 => if V.eq_dec x s then true else in_vars x xs0
  end.

Lemma in_vars_true: forall x xs,
  In x xs <-> in_vars x xs = true.
Proof.
  split; intros.
  + induction xs.
      - inversion H.
      - destruct H. subst a. simpl. destruct (V.eq_dec x x). easy. congruence. simpl. 
        destruct (V.eq_dec x a). easy. tauto.
  + induction xs.
      - discriminate.
      - simpl in H. destruct (V.eq_dec x a).
        subst. now left. right. tauto.
Qed.

Lemma in_vars_false: forall x xs,
  ~ In x xs <-> in_vars x xs = false.
Proof.
  split; intros.
  + induction xs.
      - easy. 
      - des_notin H. simpl. destruct (V.eq_dec x a); try congruence. tauto.
  + induction xs.
      - tauto. 
      - simpl in H. destruct (V.eq_dec x a). discriminate.
         apply not_in_cons. tauto.
Qed.

Fixpoint free_occur (x: V.t) (d: prop): nat :=
    match d with
    | [[ t1 = t2]]  
    | [[ t1 ∈ t2]]   => (term_occur x t1) + (term_occur x t2)
    | PAtom a => atom_occur x a
    | PFalse  
    | PTrue        => O
    | [[ ¬ P ]] => free_occur x P
    | [[ P1 /\ P2 ]]
    | [[ P1 \/ P2 ]]
    | [[ P1 -> P2 ]]
    | [[ P1 <-> P2]]  => (free_occur x P1) + (free_occur x P2)
    | [[ ∀x',P]] 
    | [[ ∃x',P]] => if V.eq_dec x x'
                      then O
                      else free_occur x P
    | [[let r xs := P in Q]] => (if in_vars x xs then O else free_occur x P) + free_occur x Q
    end.

Fixpoint pred_atom_occur(x:R.t)(a:atom):nat:=
  match a with
  | APred r => if R.eq_dec x r then S O else O
  | AApp a0 t => pred_atom_occur x a0
  end.
  
Fixpoint pred_free_occur (x: R.t) (d: prop): nat :=
    match d with
    | [[ t1 = t2]]  
    | [[ t1 ∈ t2]]   => O
    |  PAtom a => pred_atom_occur x a
    | PFalse  
    | PTrue        => O
    | [[ ¬ P ]] => pred_free_occur x P
    | [[ P1 /\ P2 ]]
    | [[ P1 \/ P2 ]]
    | [[ P1 -> P2 ]]
    | [[ P1 <-> P2]]  => (pred_free_occur x P1) + (pred_free_occur x P2)
    | [[ ∀x',P]] 
    | [[ ∃x',P]] => pred_free_occur x P
    | [[let r xs := P in Q]] => pred_free_occur x P  + (if R.eq_dec x r then O 
                                           else pred_free_occur x Q )
    end.
    
Fixpoint pred_occur (x: R.t) (d: prop): nat :=
    match d with
    | [[ t1 = t2]]  
    | [[ t1 ∈ t2]]   => O
    |  PAtom a => pred_atom_occur x a
    | PFalse  
    | PTrue        => O
    | [[ ¬ P ]] => pred_occur x P
    | [[ P1 /\ P2 ]]
    | [[ P1 \/ P2 ]]
    | [[ P1 -> P2 ]]
    | [[ P1 <-> P2]]  => (pred_occur x P1) + (pred_occur x P2)
    | [[ ∀x',P]] 
    | [[ ∃x',P]] => pred_occur x P
    | [[let r xs := P in Q]] =>(if R.eq_dec x r then S O else O) + pred_occur x P  + pred_occur x Q 
    end.
    
Fixpoint term_ustr (t:term):list ustr:=
  match t with
  | empty_set => nil
  | var x => [uvar x]
  | singleton x => term_ustr x
  | intersection x y
  | union x y => term_ustr x ++ term_ustr y
end.

Fixpoint atom_ustr (a:atom): list ustr:=
  match a with
  | APred r => [upred r]
  | AApp a0 t => atom_ustr a0 ++ term_ustr t
  end.

Fixpoint prop_ustr(d:prop):list ustr:=
  match d with
  | PEq t1 t2
  | PRel t1 t2 => term_ustr t1 ++ term_ustr t2
  | PTrue
  | PFalse => nil
  | PAtom a => atom_ustr a
  | PNot P => prop_ustr P
  | PAnd P1 P2
  | POr P1 P2
  | PImpl P1 P2
  | PIff P1 P2 => prop_ustr P1 ++ prop_ustr P2
  | PForall x P
  | PExists x P =>(uvar x)::(prop_ustr P)
  | PPredDef r xs P Q  => (upred r)::(prop_ustr Q) ++(map uvar xs) ++ prop_ustr P
  end.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Substitution                                           *)
(*                                                                   *)
(*  The definition tries to coincide with that in lambda_binding                               *)
(* ***************************************************************** *)

Inductive subst_pair: Type:=
  |  svar (x:V.t) (t:term)
  |  spred (r r0: R.t)
  |  sprop (r:R.t) (xs: list V.t) (P:prop)
 .

Definition newv (xs: list ustr): V.t:=
  match new_ustr xs variable with
  | uvar v => v
  | _ => V.default
  end.
  
Definition newr (xs: list ustr): R.t:=
  match new_ustr xs predname with
  | upred r => r
  | _ => R.default
  end.


Definition subst_task: Type := list subst_pair.

Fixpoint task_occur (x: V.t) (st:subst_task): nat:=
  match st with
  | nil => O
  | (svar s t)::st0 => var_occur x s + term_occur x t + task_occur x st0
  | (spred r1 r2):: st0 => task_occur x st0
  | (sprop r xs P)::st0 => (if in_vars x xs then O else free_occur x P) + task_occur x st0
  end.

Fixpoint pred_task_occur (r:R.t)(st:subst_task): nat:=
  match st with
  | nil => O
  | (svar x t):: st0 => pred_task_occur r st0
  | (spred r1 r2):: st0 => pred_pred_occur r r1 + pred_pred_occur r r2 + pred_task_occur r st0
  | (sprop r0 xs P):: st0 => pred_pred_occur r r0 + pred_free_occur r P + pred_task_occur r st0
  end.

Fixpoint task_term_occur (x: V.t) (st:subst_task): nat:=
  match st with
  | nil => O
  | (svar s t)::st0 => term_occur x t + task_term_occur x st0
  | (spred r1 r2):: st0 => task_term_occur x st0
  | (sprop r xs P)::st0 => (if in_vars x xs then O else free_occur x P) + task_term_occur x st0
  end.

Fixpoint pred_task_term_occur (r:R.t)(st:subst_task): nat:=
  match st with
  | nil => O
  | (svar x t):: st0 => pred_task_term_occur r st0
  | (spred r1 r2):: st0 => pred_pred_occur r r2 + pred_task_term_occur r st0
  | (sprop r0 xs P):: st0 => pred_free_occur r P + pred_task_term_occur r st0
  end.

Definition subst_pair_ustr (p:subst_pair): list ustr:=
  match p with
  | svar x t => uvar x::term_ustr t
  | spred r1 r2 => upred r1:: upred r2:: nil
  | sprop r xs P =>upred r:: map uvar xs ++ prop_ustr P
  end.
  
Definition task_ustr (st:subst_task): list ustr:=
  flat_map subst_pair_ustr st.

Fixpoint var_sub (x: V.t) (st: subst_task): term :=
  match st with
  | nil => x
  | (svar x' t):: st0 => if V.eq_dec x x' then t else var_sub x st0
  | _:: st0 => var_sub x st0
  end.
  
Fixpoint pred_sub (r:R.t) (st:subst_task): R.t :=
  match st with
  | nil => r
  | (spred r1 r2):: st0 => if R.eq_dec r r1 then r2 else pred_sub r st0
  | _:: st0 => pred_sub r st0
  end.

Fixpoint term_sub (st: subst_task) (t: term) : term:=
  match t with
  | [[∅]]=> [[∅]]
  | var x => var_sub x st
  | [[ {x} ]]=> singleton (term_sub st x)
  | [[ x ∪ y]] => union (term_sub st x) (term_sub st y)
  | [[ x ∩ y]] => intersection (term_sub st x) (term_sub st y)
  end.
  
Fixpoint atom_var_sub (st:subst_task)(a:atom): atom:=
  match a with
  | APred r => APred r
  | AApp a0 t => AApp (atom_var_sub st a0) (term_sub st t)
  end.

Definition reducev (x: V.t)(st:subst_task): subst_task:=
  filter (fun p => match p with 
                        | svar s _ => if V.eq_dec x s then false else true 
                        | _ => true end) st.
   
Fixpoint list_reducev (xs:list V.t)(st:subst_task): subst_task:=
  match xs with
  | nil => st
  | x::xs0 => reducev x (list_reducev xs0 st)
end.

  
Definition reducer (r: R.t)(st:subst_task): subst_task:=
  filter (fun p => match p with 
                        | spred r1 _ => if R.eq_dec r r1 then false else true 
                        | sprop r0 _ _ => if R.eq_dec r r0 then false else true  
                        | _ => true end) st.

Fixpoint vars_new_st (d:prop) (xs: list V.t) (st:subst_task): subst_task:=
  match xs with
  | nil => st
  | x::xs0 => let st':= reducev x st in
                    match task_term_occur x st' with
                    | O => vars_new_st d xs0 st'
                    | _ => let x':= newv ((map uvar xs)++(prop_ustr d)++(task_ustr st')) in
                                 vars_new_st d xs0 ((svar x x')::st')
                    end
  end.
  
Fixpoint  vars_new_xs (d:prop)(xs:list V.t) (st:subst_task): list V.t:=
  match xs with
  | nil => nil
  | x::xs0 => let st':= reducev x st in
                     match task_term_occur x st' with
                     | O => x:: (vars_new_xs d xs0 st')
                     | _ =>  let x':= newv ((map uvar xs)++(prop_ustr d)++(task_ustr st')) in
                                  x':: (vars_new_xs d xs0 ((svar x x')::st'))
                    end
  end.

(*** Only substitute variables ***)
Fixpoint prop_var_sub (st: subst_task) (d: prop): prop :=
    match d with
    | [[ t1 = t2]]  => PEq (term_sub st t1) (term_sub st t2)
    | [[ t1 ∈ t2]]   => PRel (term_sub st t1) (term_sub st t2)
    | PAtom a=> PAtom (atom_var_sub st a)
    | PTrue     => PTrue
    | PFalse    => PFalse
    |  [[ ¬ P ]]  => PNot (prop_var_sub st P)
    |  [[ P1 /\ P2 ]]=> PAnd (prop_var_sub st P1) (prop_var_sub st P2)
    | [[ P1 \/ P2 ]] => POr (prop_var_sub st P1) (prop_var_sub st P2)
    | [[ P1 -> P2 ]] => PImpl (prop_var_sub st P1) (prop_var_sub st P2)
    | [[ P1 <-> P2]] => PIff (prop_var_sub st P1) (prop_var_sub st P2)
    | [[ ∀x,P]]  => let st':= reducev x st in
                            match task_term_occur x st' with
                            | O => PForall x (prop_var_sub st' P)
                            | _ => let x' := newv (prop_ustr d ++ task_ustr st')  in
                                         PForall x' (prop_var_sub (cons (svar x x') st') P)
                            end
    | [[ ∃x,P]]  => let st':= reducev x st in
                            match task_term_occur x st' with
                            | O => PExists x (prop_var_sub st' P)
                            | _ => let x' := newv (prop_ustr d ++ task_ustr st')  in
                                         PExists x' (prop_var_sub (cons (svar x x') st') P)
                     end
    | [[ let r xs := P in Q]] => let xs':= vars_new_xs P xs st in
                                            let st':= vars_new_st P xs st in
                                            PPredDef r xs' (prop_var_sub st' P) (prop_var_sub st Q)
    end.       

Fixpoint atom_pred(a:atom): R.t:=
  match a with
  | APred r => r
  | AApp a0 t => atom_pred a0
  end.
  
Fixpoint construct_atom(a:atom)(ts:list term):=
  match ts with 
  | nil => a
  | t::ts0 => construct_atom (AApp a t) ts0
  end.

(* Fixpoint pred_extended_prop (st:subst_task) (r:R.t): option ((list V.t)*prop):=
  match st with
  | nil => None
  | (spred r1 r2):: st0 => if R.eq_dec r r1 then None else pred_extended_prop st0 r
  | (sprop r0 xs P):: st0 => if R.eq_dec r r0 then (Some (xs,P)) else pred_extended_prop st0 r
  | _ :: st0 => pred_extended_prop st0 r
  end.

Definition atom_extended_prop (st: subst_task)(a:atom):=
  pred_extended_prop st (atom_pred a). *)
  
Fixpoint instantiate_var_binder (P:prop) (xs: list V.t) (ts:list term): prop:=
  match xs, ts with
  | x::xs0, t::ts0 =>  let st:= [(svar x t)] in
                               instantiate_var_binder (prop_var_sub (vars_new_st P xs0 st) P) (vars_new_xs P xs0 st) ts0
  | _ , _ => P
  end.

Fixpoint extend_pred (r:R.t)(ts:list term)(st:subst_task):=
  match st with
  | nil => PAtom (construct_atom (APred r) ts)
  | (spred r1 r2):: st0 => if R.eq_dec r r1 then  PAtom (construct_atom (APred r2) ts)
                                       else extend_pred r ts st0
  | (sprop r0 xs P)::st0 => if R.eq_dec r r0 then instantiate_var_binder P xs ts
                                       else extend_pred r ts st0
  | _:: st0 => extend_pred r ts st0
  end.
  
Fixpoint atom_sub_aux (a:atom)(ts:list term)(st:subst_task):=
  match a with
  | APred r => extend_pred r ts st
  | AApp a0 t => atom_sub_aux a0 ((term_sub st t)::ts) st
  end.
  
Definition atom_sub (st: subst_task)(a:atom):prop:=
 atom_sub_aux a nil st.

Fixpoint prop_sub (st: subst_task) (d: prop): prop :=
    match d with
    | [[ t1 = t2]]  => PEq (term_sub st t1) (term_sub st t2)
    | [[ t1 ∈ t2]]   => PRel (term_sub st t1) (term_sub st t2)
    | PAtom a => atom_sub st a
    | PTrue     => PTrue
    | PFalse    => PFalse
    |  [[ ¬ P ]]  => PNot (prop_sub st P)
    |  [[ P1 /\ P2 ]]=> PAnd (prop_sub st P1) (prop_sub st P2)
    | [[ P1 \/ P2 ]] => POr (prop_sub st P1) (prop_sub st P2)
    | [[ P1 -> P2 ]] => PImpl (prop_sub st P1) (prop_sub st P2)
    | [[ P1 <-> P2]] => PIff (prop_sub st P1) (prop_sub st P2)
    | [[ ∀x,P]]  => let st':= reducev x st in
                            match task_term_occur x st' with
                            | O => PForall x (prop_sub st' P)
                            | _ => let x' := newv (prop_ustr d ++ task_ustr st')  in
                                         PForall x' (prop_sub (cons (svar x  x') st') P)
                            end
    | [[ ∃x,P]]  => let st':= reducev x st in
                            match task_term_occur x st' with
                            | O => PExists x (prop_sub st' P)
                            | _ => let x' := newv (prop_ustr d ++ task_ustr st')  in
                                         PExists x' (prop_sub (cons (svar x  x') st') P)
                     end
    | [[ let r xs := P in Q]] => let st1:= reducer r st in 
                                             let xs':= vars_new_xs P xs st in
                                             let st2:= vars_new_st P xs st in
                                             match pred_task_term_occur r st1 with
                                             | O => PPredDef r xs'  (prop_sub st2 P)  (prop_sub st1 Q) 
                                             | _ => let r':= newr ((upred r)::(prop_ustr Q) ++ task_ustr st1) in
                                                        PPredDef r' xs' (prop_sub st2 P)  (prop_sub ((spred r r')::st1) Q) 
                                             end
    end.             
    
Declare Scope sugar_subst_scope.
Delimit Scope sugar_subst_scope with ss.

Notation "x |-> t" := (svar x t) (in custom sset at level 17, no associativity): sugar_subst_scope.

Notation "r1 '|-r->' r2" := (spred r1 r2) (in custom sset at level 17, no associativity): sugar_subst_scope.

Notation "r '|->' 'λ' xs , t" := (sprop r xs t) (in custom sset at level 17, no associativity): sugar_subst_scope.

Notation "P [ xt ]" :=
  (prop_sub ( cons xt%ss nil ) P%s) (in custom sset at level 20, no associativity):Sugar_scope.
  
Notation "P [ xt1 ; xt2 ; .. ; xtn ]" :=
  (prop_sub ( cons xt1%ss  (cons xt2%ss .. (cons xtn%ss nil) .. ) ) P%s) (in custom sset at level 20,  no associativity): Sugar_scope.

Inductive only_var_sub: subst_pair -> Prop:=
 | only_var_sub_constructor: forall x t, only_var_sub (svar x t).

Lemma construct_atom_app: forall a t ts,
   construct_atom (AApp a t) ts = construct_atom a (t::ts).
Proof. intros; now destruct a. Qed.
  
Lemma reducev_Forall: forall x P (st: subst_task),
  Forall P st ->
  Forall P (reducev x st).
Proof. 
  intros. induction st. easy. destruct a.
  + simpl. forall_cons H. destruct (V.eq_dec x x0) . 
      - tauto.
      - apply Forall_cons; tauto.
  + forall_cons H. simpl. apply Forall_cons; tauto.
  + forall_cons H. simpl. apply Forall_cons; tauto.
Qed.

Lemma reducer_Forall: forall x P (st: subst_task),
  Forall P st ->
  Forall P (reducer x st).
Proof.
  intros. induction st. easy. destruct a.
  + simpl. forall_cons H. apply Forall_cons; tauto. 
  + forall_cons H. simpl. destruct (R.eq_dec x r).
      - tauto.
      - apply Forall_cons; tauto.
  + forall_cons H. simpl. destruct (R.eq_dec x r).
      - tauto.
      - apply Forall_cons; tauto.
Qed.

Lemma reducer_only_var_sub: forall r st,
  Forall only_var_sub st ->
  reducer r st = st.
Proof.
  intros. induction st.
  + easy.
  + forall_cons H. inversion H; subst. simpl. f_equal. tauto.
Qed.

Lemma pred_task_term_occur_only_var_sub: forall r st,
  Forall only_var_sub st ->
  pred_task_term_occur r st = 0.
Proof.
  intros. induction st.
  + easy.
  + forall_cons H. inversion H; subst. tauto.
Qed.

Lemma vars_new_st_only_var_sub: forall p xs st,
  Forall only_var_sub st -> 
  Forall only_var_sub (vars_new_st p xs st).
Proof.
  intros p xs. induction xs; intros.
  + easy.
  + simpl. destruct (task_term_occur a (reducev a st)). apply IHxs. 
      now apply reducev_Forall. apply IHxs. apply Forall_cons.
      constructor. now apply reducev_Forall.
Qed.

Lemma atom_var_sub_atom_sub_aux: forall a ts st,
  Forall only_var_sub st ->
  PAtom (construct_atom (atom_var_sub st a) ts) = atom_sub_aux a ts st.
Proof.
  induction a; intros.
  + simpl. induction st.
      - easy.
      - forall_cons H. inversion H; subst. tauto.
  + simpl. rewrite construct_atom_app. now apply IHa.
Qed.

Corollary atom_var_sub_atom_sub: forall a st,
  Forall only_var_sub st ->
  PAtom (atom_var_sub st a) = atom_sub st a.
Proof. intros. pose proof atom_var_sub_atom_sub_aux a nil st. tauto. Qed.

Lemma prop_var_sub_prop_sub: forall p st,
  Forall only_var_sub st ->
  prop_var_sub st p = prop_sub st p.
Proof.
  induction p; intros; try easy; simpl; try f_equal; try auto.
  + now apply atom_var_sub_atom_sub.
  + destruct (task_term_occur x (reducev x st)).
     - f_equal. apply IHp. now apply reducev_Forall. 
     - f_equal. apply IHp. apply Forall_cons. constructor. now apply reducev_Forall.
  + destruct (task_term_occur x (reducev x st)).
     - f_equal. apply IHp. now apply reducev_Forall.
     - f_equal. apply IHp. apply Forall_cons. constructor. now apply reducev_Forall.
  + rewrite reducer_only_var_sub. rewrite pred_task_term_occur_only_var_sub.
      f_equal. apply IHp1. now apply vars_new_st_only_var_sub. auto. easy. easy.
Qed.


(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Alpha equivalence                                                *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Definition binder_pair:Type:= ustr * ustr * bool.

Definition binder_list: Type:= list binder_pair.

Definition binder_update (x:ustr)(y:ustr)(bd:binder_pair):binder_pair:=
  let '(x0,y0,b):= bd in
  if zerop (ustr_occur x x0 + ustr_occur y y0) then bd else (x0,y0,false).

Definition update (x y: ustr)(st:binder_list):=
  map (fun bd => binder_update x y bd) st.
  
Fixpoint var_list_update (xs ys: list V.t)(st: binder_list):binder_list:=
  match xs, ys with
  | nil, nil => st
  | x::xs0, y::ys0 => var_list_update xs0 ys0 ((uvar x,uvar y,true)::update x y st)
  | _ , _ => st
  end.
  
Definition binder_l (st:binder_list):list ustr:=
  map (fun x => fst (fst x)) st.

Definition binder_r (st:binder_list): list ustr:=
  map (fun x => snd (fst x)) st.

Inductive term_alpha_eq: binder_list -> term -> term -> Prop:=
 | empty_aeq: forall bd, term_alpha_eq bd empty_set empty_set
 | var_aeq1: forall bd (s1 s2: V.t),
                 In (uvar s1,uvar s2,true) bd ->
                 term_alpha_eq bd (var s1) (var s2)
 | var_aeq2: forall bd (s:V.t),
                ~ In (uvar s) (binder_l bd) ->
                ~ In (uvar s) (binder_r bd) ->
                term_alpha_eq bd (var s) (var s)
 | singleton_aeq: forall bd t1 t2,
                term_alpha_eq bd t1 t2 ->
                term_alpha_eq bd (singleton t1)(singleton t2)
 | union_aeq: forall bd t1 t2 t3 t4,
                term_alpha_eq bd t1 t3 ->
                term_alpha_eq bd t2 t4 ->
                term_alpha_eq bd (union t1 t2) (union t3 t4) 
 | intersection_aeq: forall bd t1 t2 t3 t4,
                term_alpha_eq bd t1 t3 ->
                term_alpha_eq bd t2 t4 ->
                term_alpha_eq bd (intersection t1 t2) (intersection t3 t4)
. 

Inductive atom_alpha_eq: binder_list -> atom -> atom -> Prop:=
 | APred_aeq1: forall bd r1 r2,
                In (upred r1, upred r2, true) bd ->
                atom_alpha_eq bd (APred r1) (APred r2)
 | APred_aeq2: forall bd r,
                ~ In (upred r) (binder_l bd) ->
                ~ In (upred r) (binder_r bd) ->
                atom_alpha_eq bd (APred r) (APred r)
 | AApp_aeq: forall bd a1 a2 t1 t2,
                atom_alpha_eq bd a1 a2 ->
                term_alpha_eq bd t1 t2 ->
                atom_alpha_eq bd (AApp a1 t1) (AApp a2 t2)
.

Inductive alpha_eq: binder_list -> prop -> prop -> Prop:=
 | PEq_aeq: forall bd t1 t2 t3 t4,
                term_alpha_eq bd t1 t3 ->
                term_alpha_eq bd t2 t4 ->
                alpha_eq bd (PEq t1 t2) (PEq t3 t4) 
 | PRel_aeq: forall bd t1 t2 t3 t4,
                term_alpha_eq bd t1 t3 ->
                term_alpha_eq bd t2 t4 ->
                alpha_eq bd (PRel t1 t2) (PRel t3 t4)
 | PAtom_aeq: forall bd a1 a2,
                atom_alpha_eq bd a1 a2 ->
                alpha_eq bd (PAtom a1) (PAtom a2) 
 | PFalse_aeq: forall bd,
                alpha_eq bd PFalse PFalse
 | PTrue_aeq: forall bd,
                alpha_eq bd PTrue PTrue
 | PNot_aeq: forall bd P1 P2,
                alpha_eq bd P1 P2 ->
                alpha_eq bd (PNot P1) (PNot P2)
 | PAnd_aeq: forall bd P1 P2 P3 P4,
                alpha_eq bd P1 P3 ->
                alpha_eq bd P2 P4 ->
                alpha_eq bd (PAnd P1 P2) (PAnd P3 P4) 
 | POr_aeq: forall bd P1 P2 P3 P4,
                alpha_eq bd P1 P3 ->
                alpha_eq bd P2 P4 ->
                alpha_eq bd (POr P1 P2) (POr P3 P4) 
 | PImpl_aeq: forall bd P1 P2 P3 P4,
                alpha_eq bd P1 P3 ->
                alpha_eq bd P2 P4 ->
                alpha_eq bd (PImpl P1 P2) (PImpl P3 P4) 
 | PIff_aeq: forall bd P1 P2 P3 P4,
                alpha_eq bd P1 P3 ->
                alpha_eq bd P2 P4 ->
                alpha_eq bd (PIff P1 P2) (PIff P3 P4)
 | PForall_aeq: forall (x x': V.t) bd P1 P2,
               alpha_eq ((uvar x,uvar x',true)::(update x x' bd)) P1 P2 ->
               alpha_eq bd (PForall x P1) (PForall x' P2)
 | PExists_aeq: forall (x x': V.t) bd P1 P2,
               alpha_eq ((uvar x,uvar x',true)::(update x x' bd)) P1 P2 ->
               alpha_eq bd (PExists x P1) (PExists x' P2)
 | PPredDef_aeq: forall bd (r1 r2: R.t) (xs1 xs2:list V.t) P1 P2 Q1 Q2,
                length xs1 = length xs2 ->
                alpha_eq (var_list_update xs1 xs2 bd) P1 P2 ->
                alpha_eq ((upred r1, upred r2, true):: (update (upred r1) (upred r2) bd)) Q1 Q2 ->
                alpha_eq bd [[let r1 xs1:= P1 in Q1]] [[let r2 xs2:= P2 in Q2]] 
.

Definition aeq (P Q:prop):= alpha_eq nil P Q.

Fixpoint in_ustr_binder_list(x y:ustr)(l:binder_list):bool:=
  match l with
  | nil => false
  | (x0,y0,b)::ls => match ustr_occur x x0, ustr_occur y y0 with
                                | S _ , S _ => if Sumbool.sumbool_of_bool b then true 
                                                       else in_ustr_binder_list x y ls
                                | _ , _ => in_ustr_binder_list x y ls
                                end
 end.


Fixpoint not_in_ustr_binder_list(x:ustr)(l:binder_list):bool:=
  match l with
  | nil => true
  | (x0,y0,b)::ls => match ustr_occur x x0, ustr_occur x y0 with
                              | O, O => not_in_ustr_binder_list x ls
                              | _ , _ => false
                              end
  end.
  
Lemma in_ustr_binder_list_correct: forall x y bd,
 In (x,y,true) bd <->  in_ustr_binder_list x y bd = true.
Proof.
  split; intros.
  + induction bd.
      - inversion H.
      - destruct a as  [ [x0 y0] b0].
         destruct H.
        * injection H as H; subst. simpl. 
           destruct (ustr_occur_eq x x); destruct (ustr_occur_eq y y); congruence. 
        * simpl. destruct (ustr_occur x x0); destruct (ustr_occur y y0); try tauto.
           destruct (Sumbool.sumbool_of_bool b0); tauto.
  + induction bd.
      - discriminate H.
      - destruct a as [ [x0 y0] b0]. simpl in H.
         destruct (ustr_occur_eq x x0); destruct (ustr_occur_eq y y0);[|right;tauto..].
         destruct (Sumbool.sumbool_of_bool b0).
         subst. now left. right. tauto.
Qed.
  
Lemma not_in_ustr_binder_list_correct: forall x bd,
  ~ In x (binder_l bd) /\ ~ In x (binder_r bd) <-> not_in_ustr_binder_list x bd = true.
Proof.
  split; intros.
  + destruct H. induction bd.
      - reflexivity.
      - destruct a as [ [x0 y0] b0]. simpl in H. simpl in H0.
         apply deMorgan1 in H. destruct H.
         apply deMorgan1 in H0. destruct H0.
         simpl. destruct (ustr_occur_eq x x0); destruct (ustr_occur_eq x y0); try congruence.
         now apply IHbd.
  + induction bd.
      - now constructor.
      - destruct a as [ [x0 y0]  b0 ].
        simpl in H.  destruct (ustr_occur_eq x x0); destruct (ustr_occur_eq x y0); try discriminate.
        split; apply not_in_cons; tauto.
Qed.

Fixpoint term_alpha_eqb(l:binder_list)(t1 t2:term):bool:=
  match t1,t2 with
  | empty_set, empty_set => true
  | var x, var y => if V.eq_dec x y then in_ustr_binder_list (uvar x) (uvar y) l || not_in_ustr_binder_list (uvar x) l
                              else in_ustr_binder_list (uvar x) (uvar y) l
  | singleton x, singleton y => term_alpha_eqb l x y
  | intersection x1 x2, intersection y1 y2
  | union x1 x2, union y1 y2 => term_alpha_eqb l x1 y1 && term_alpha_eqb l x2 y2
  | _ , _ => false
  end.

Lemma term_alpha_eq_term_alpha_eqb: forall t1 t2 bd,
  term_alpha_eq bd t1 t2 <-> term_alpha_eqb bd t1 t2 = true.
Proof.
  split; intros.
  + induction H.
      - reflexivity.
      - simpl. destruct (V.eq_dec s1 s2).
        * subst. apply in_ustr_binder_list_correct in H.
            rewrite H. apply orb_true_l.
        * now apply in_ustr_binder_list_correct.
      - simpl. destruct (V.eq_dec s s); try congruence.
        assert (not_in_ustr_binder_list s bd = true) by now apply not_in_ustr_binder_list_correct.   
        rewrite H1. apply orb_true_r.
      - easy.
      - simpl. rewrite IHterm_alpha_eq1. now rewrite IHterm_alpha_eq2.
      - simpl. rewrite IHterm_alpha_eq1. now rewrite IHterm_alpha_eq2. 
   + revert t2 bd H. induction t1; intros; destruct t2; try discriminate H. 
       - simpl in H. destruct (V.eq_dec v v0).
         * subst. apply orb_prop in H. destruct H.
            ++ constructor 2. now apply in_ustr_binder_list_correct.
            ++ constructor 3; now apply not_in_ustr_binder_list_correct.
         * constructor 2. now apply in_ustr_binder_list_correct.
      - constructor.
      - constructor. auto.
      - simpl in H. apply andb_prop in H. destruct H.  constructor; auto.
      - simpl in H. apply andb_prop in H. destruct H.  constructor; auto.
Qed. 


Fixpoint atom_alpha_eqb(l:binder_list)(t1 t2:atom):bool:=
  match t1, t2 with
  | APred x, APred y => if R.eq_dec x y then in_ustr_binder_list (upred x) (upred y) l || 
                                        not_in_ustr_binder_list (upred x) l
                                      else in_ustr_binder_list (upred x) (upred y) l
  | AApp a1 t1, AApp a2 t2 => term_alpha_eqb l t1 t2 && atom_alpha_eqb l a1 a2
  | _ , _ => false
  end.
  
Lemma atom_alpha_eq_atom_alpha_eqb: forall t1 t2 bd,
  atom_alpha_eq bd t1 t2 <-> atom_alpha_eqb bd t1 t2 = true.
Proof.
  split; intros.
  + induction H.
      - simpl. destruct (R.eq_dec r1 r2).
        * subst. apply in_ustr_binder_list_correct in H. rewrite H. apply orb_true_l.
        * now apply in_ustr_binder_list_correct.
      - simpl. destruct (R.eq_dec r r); try congruence.
        assert (not_in_ustr_binder_list (upred r) bd = true) by now apply not_in_ustr_binder_list_correct.   
        rewrite H1. apply orb_true_r.
      - simpl. apply term_alpha_eq_term_alpha_eqb in H0. rewrite H0. rewrite IHatom_alpha_eq. easy.
   + revert t2 bd H. induction t1; intros; destruct t2; try discriminate H. 
       - simpl in H. destruct (R.eq_dec r r0).
         * subst. apply orb_prop in H. destruct H.
            ++ constructor. now apply in_ustr_binder_list_correct.
            ++ constructor 2; now apply not_in_ustr_binder_list_correct.
         * constructor. now apply in_ustr_binder_list_correct.
      - simpl in H. apply andb_prop in H. destruct H.  constructor; auto. now apply term_alpha_eq_term_alpha_eqb.
Qed.

Fixpoint vars_same_length (l1 l2: list V.t):=
  match l1, l2 with
  | nil, nil => true
  | _::ls1, _::ls2 => vars_same_length ls1 ls2
  | _ , _ => false
  end.
  
Lemma vars_same_length_correct: forall l1 l2,
  vars_same_length l1 l2 = true <-> length l1 = length l2.
Proof.
  split; intros.
  + revert l2 H. induction l1; intros; destruct l2; try discriminate. easy. simpl. f_equal. simpl in H. auto.
  + revert l2 H. induction l1; intros; destruct l2; try discriminate. easy. simpl. simpl in H. injection H as H. auto.
Qed.

Fixpoint alpha_eqb(l:binder_list)(P Q:prop):bool:=
  match P,Q with
  | [[t1 = t2]], [[t3=t4]]
  | [[t1 ∈ t2]], [[t3 ∈ t4]] => term_alpha_eqb l t1 t3 && term_alpha_eqb l t2 t4
  | PAtom a1, PAtom a2 => atom_alpha_eqb l a1 a2
  | PTrue, PTrue
  | PFalse, PFalse => true
  | [[¬ P1]], [[¬ Q1]] => alpha_eqb l P1 Q1 
  | [[P1 /\ P2]], [[Q1 /\ Q2]]
  | [[P1 \/ P2]],  [[Q1 \/ Q2]]
  | [[P1 -> P2]],  [[Q1 -> Q2]]
  | [[P1 <-> P2]],  [[Q1 <-> Q2]] => alpha_eqb l P1 Q1 && alpha_eqb l P2 Q2 
  | [[∀x, P1]], [[∀y, Q1]]
  | [[∃x, P1]],  [[∃y, Q1]]=> alpha_eqb ((uvar x,uvar y,true)::(update x y l)) P1 Q1
  | [[let r1 xs1:= P1 in Q1]], [[let r2 xs2:= P2 in Q2]] =>
        alpha_eqb (var_list_update xs1 xs2 l) P1 P2 &&
        alpha_eqb ((upred r1, upred r2, true)::(update (upred r1) (upred r2) l)) Q1 Q2 &&
        vars_same_length xs1 xs2
  | _, _ => false
  end.
  
Lemma alpha_eq_alpha_eqb: forall P Q bd,
  alpha_eq bd P Q <-> alpha_eqb bd P Q = true.
Proof.
  split; intros.
  + induction H; simpl; try rewrite IHalpha_eq1; try rewrite IHalpha_eq2; try easy.
      - simpl. apply term_alpha_eq_term_alpha_eqb in H.
        apply term_alpha_eq_term_alpha_eqb in H0.
        rewrite H. rewrite H0. easy.
      - simpl. apply term_alpha_eq_term_alpha_eqb in H.
        apply term_alpha_eq_term_alpha_eqb in H0.
        rewrite H. rewrite H0. easy.
      - now apply atom_alpha_eq_atom_alpha_eqb.
      - apply vars_same_length_correct in H. now rewrite H.
  + revert Q bd H. induction P; intros; destruct Q; try discriminate H; simpl in H; 
      try apply andb_prop in H; try constructor; auto; 
        match type of H with
        | _ /\ _ => destruct H; auto; try now apply term_alpha_eq_term_alpha_eqb
        | _ =>idtac
        end.
      - now apply atom_alpha_eq_atom_alpha_eqb.
      - now apply vars_same_length_correct.
      - apply andb_prop in H; destruct H; auto. 
      - apply andb_prop in H; destruct H; auto.  
Qed.
  
Definition aeqb(P Q:prop):bool:= alpha_eqb nil P Q.

Corollary aeq_aeqb: forall P Q,
  aeq P Q <-> aeqb P Q = true.
Proof. intros. now apply alpha_eq_alpha_eqb. Qed.

Close Scope Sugar_scope.

End DemoSugarFOL.