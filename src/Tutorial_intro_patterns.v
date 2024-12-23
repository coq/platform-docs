(** * Tutorial: Intro Patterns

  *** Main contributors

    - Thomas Lamiaux

  *** Summary

  In this tutorial, we explain how to use intro patterns to write more concise code.

  *** Table of content

      - 1. Introducing Variables
      - 2. Destructing Variables
      - 3. Rewriting and Injection
      - 3. Applying Lemma
      - 4.

  *** Prerequisites

    Needed:
    - No Prerequisites

    Not Needed:
    - No Prerequisites

    Installation:
  - Available by default with coq

*)

From Coq Require Import List. 
Import ListNotations.


(** ** 1. Introducing Variables *)

(** The basic tactic to introduces variables is [intros]. In its most basic forms
    [intros x y ... z] will introduce as much variables as mentioned with the 
    names specified [x], [y], ..., [z]. Note, it will fail if one of the names 
    is already used.
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros n m H.
Abort.

Goal forall n m, n < m -> n <= m.
Proof.
  Fail intros n n H.
Abort.

(** It can happen that we have an hypothesis to introduce that is not useful
    to our proof. In this case, rather than introducing it we would rather like
    to directly forget it. This is possible using the wildcard pattern [_].
    Note that logically it is not possible to forget an hypothesis that appear 
    in the conclusion.
*)

Goal forall n m, n = 0 -> n < m -> n <= m.
Proof.
  intros n m _ H.
Abort.

Goal forall n m, n < m -> n <= m.
Proof.
  Fail intros _ m H.
Abort.


(** In some cases, we do not wish to choose a name and would rather have Coq to
    choose a name for us. This is possible with the [?] pattern. 
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros n m ?.
Abort.

(** However, be careful that referring explicitly to auto-generated names in a
    proof is bad practice as later modification to the file could change the
    generated names, and hence break the proof. This can happen very fast.
    Auto-generated names should hence only be used in combination with tactic
    like [assumption] that do not rely on names. 
*)

(** Similarly, it happens that we want to introduce all the variables, and 
    do not want to name them. In this case, it possible to simply write [intros]
    or as an alias [intros **]
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros.
Abort.

Goal forall n m, n < m -> n <= m.
Proof.
  intros **.
Abort.

(** As a variant [intros *] will introduce all the variables that do no appear 
    dependently in the rest of the goal. In this example, it will hence introduce
    [n] and [m] but not [n < m] as it depends on [n] and [m]. 
*)

Goal forall n m, n < m -> n <= m.
Proof.
  intros *.
Abort.
  
(** An important difference between [intros] and [intros ?x] is that [intros] 
    is to be understood as "introduce as much variables as you see" whereas 
    [intros ?X] is to be understood as "introduce exactly one variable".
    [intros] will hence introduce as much variables as possible without 
    simplifying the goal, whereas [intros ?x] will first compute the head normal 
    form before trying to introduce a variable.

    For instance, consider the definition that a relation is reflexive. 
*)

Definition Reflexive {A} (R : A -> A -> Prop) := forall a, R a a.

(** If we try to prove that logical equivalence is reflexive by using [intros] 
    then nothing will happen as [Reflexive] is a constant, and it needs to 
    be unfolded for a variable to introduce to appear. 
    However, as [intros ?x] simplify the goal first, it will succed and progress:
*)

Goal Reflexive (fun P Q => P <-> Q).
  Fail progress intros. intros P. 
Abort.



(** ** 2. Destructing Variables *)

(* constructor *)
Definition and_comm : forall P Q, P /\ Q -> Q /\ P.
  intros P Q [p q]. split.
  + exact q.
  + exact p.
Qed.




(* disjunction *)
Definition or_comm : forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q [p | q].
  + right. exact p.
  + left. exact q.
Qed.



(** ** 3. Rewriting Lemmas *)

(** It is common when introducing variables that we introduce an equality that 
    we wish to later rewite the goal by. *)
Goal forall n m, n = 0 -> n + m = m. 
Proof.
  intros n m H. rewrite H. cbn. reflexivity.
Qed.

(** It is so common that there is an intro patterns to do this automatically for us. 
    Writing [->] or [<-] will introduce [H] then rewrite in the goal then 
    clear it from the context.  *)
Goal forall n m, n = 0 -> n + m = m. 
Proof.
  intros n m ->. cbn. reflexivity.
Qed.

Goal forall n m, 0 = n -> n + m = m. 
Proof.
  intros n m <-. cbn. reflexivity.
Qed.

(** It will also rewrite the variable if it is present in the context. *)

Goal forall n m p, n + p = m -> n = 0 -> p = m. 
Proof.
  intros n m p H. intros ->. cbn in *. apply H.
Qed.

(* injection *)
Goal forall n m, S n = S 0 -> n + m = m.
  intros n m H. injection H. intros H'. rewrite H'. cbn. reflexivity.
Qed.

Goal forall n m, S n = S 0 -> n + m = m.
  intros n m [=]. rewrite H0. cbn. reflexivity.
Qed.

Goal forall n m, S n = S 0 -> n + m = m.
  intros n m [= ->]. cbn. reflexivity.
Qed.



(* 4. Views *)


Theorem app_eq_unit {A} (x y:list A) (a:A) :
    x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
Proof.
  destruct x; cbn.
  - intros ->. left. easy.
  - intros [= -> [-> ->]%app_eq_nil]. right. easy.
Qed. 