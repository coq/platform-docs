(** * Tutorial: Intro Patterns

  *** Main contributors

    - Thomas Lamiaux

  *** Summary

  In this tutorial, we explain how to use intro patterns to write more concise code.

  *** Table of content

      - 1. Introducing Variables
      - 2. Destructing Variables
      - 3. Rewriting and Injection
      - 4. Simplifying Equalities 
      - 5. Applying Lemmas

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

(** It is particularly practical to introduce type variables on which the goal 
    depends but on wish we do not want to perform any specific action but introduction 
 *)

Goal forall P Q, P /\ Q -> Q /\ P.
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


(** ** 2. Destructing Variables

  When proving properties, it is very common to introduce variables only to
  pattern-match on them just after, e.g to properties about an inductive type 
  or simplify an inductively defined function:
*)

Goal forall P Q, P /\ Q -> Q /\ P.
  intros P Q x. destruct x. split.
  + assumption.
  + assumption.
Qed.

Goal forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q x. destruct x.
  + right. assumption.
  + left. assumption.
Qed.
  
(** Consequently, Coq as special intro patterns [ [] ] to introduce and pattern
    match on a variable at the same time. If the inductive type only has one
    constructor like [/\], it suffices to list the names of the variables:
*)

Goal forall P Q, P /\ Q -> Q /\ P.
  intros P Q [p q]. split.
  + assumption.
  + assumption.
Qed.

(** In the general case with several constructors, it suffices to add branches 
    delimited by [ | ] in the pattern for each constructors:
*)

Goal forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q [p | q].
  + right. assumption.
  + left. assumption.
Qed.

(** Note that destructing over [False] expects nothing no branche as [False] has
    no constructors, and that it solves the goal automatically:  
*)

Goal forall P, False -> P.
Proof.
  intros P [].
Qed.

(** It is further possible to nest the intro-patterns when inductive type are 
    nested into each other, e.g. like a sequence of 
*)

Goal forall P Q R, P /\ Q /\ R -> R /\ Q /\ P.
  intros P Q R [p [q r]].
Abort.

(** In practice, two patterns comes up so often that they have dedicated patterns. 
    The first one is for iterated binary inductive types like [/\]. 
    Rather than having to destruct recursively  as [ [p [q [r h]]] ], we can 
    instead simply write [p & q & r & h]: *)

Goal forall P Q R H, P /\ Q /\ R /\ H -> H /\ R /\ Q /\ P.
Proof.
  intros * (p & q & r & h). 
Abort.

(** The second pattern is for inductive types that only have one constructor, 
    like records. In this case, it is possible to write [(a, b, ..., d)] rather 
    than [ [a b ... d]]. The interrest is that it enables to preserves [let-in]
    if there are any:  
*)

(* Record Foo := {
  foo1 : nat; 
  foo2 : nat;
  foo12 := foo1 + foo2; 
  foo_inf : foo12 = 10
}. *)

Inductive Foo := 
  foo : forall n m, let p := n + m in p = 10 -> Foo.

Goal Foo -> {n & {m | n + m = 10}}.
Proof. intros (n, m, H). Abort.

Goal Foo -> {n & {m | n + m = 10}}.
Proof. intros [n m H]. Abort.

(* TO FIX !!! => do not match refman ! *)


(** ** 3. Rewriting Lemmas *)

(** It is common when introducing variables that we introduce an equality that 
    we wish to later rewrite: 
*)

Goal forall n m, n = 0 -> n + m = m. 
Proof.
  intros n m H. rewrite H. cbn. reflexivity.
Qed.

(** It is so common that there is an intro patterns dedicated to that.
    Writing [->] or [<-] will introduce [H] then rewrite it and in the context,
    then clear it from the context. 
*)

Goal forall n m p, n + p = m -> n = 0 -> p = m. 
Proof.
  intros n m p H ->. cbn in *. apply H.
Qed.

Goal forall n m p, n + p = m -> 0 = n -> p = m. 
Proof.
  intros n m p H <-. cbn in *. apply H.
Qed.

(** ** 4. Simplifying Equalities 

  It is also very common that we have an equality as to introduce .
  Most often, we want to simplify this equality using [injection] then rewrite 
  by it. 
*) 

Goal forall n m, S n = S 0 -> n + m = m.
  intros n m H. injection H. intros H'. rewrite H'. cbn. reflexivity.
Qed.

(** This is possible by using the [ [=] ] pattern that will introduce 
    an equality then simplify it with [injection]:
 *)

Goal forall n m, S n = S 0 -> n + m = m.
  intros n m [=]. rewrite H0. cbn. reflexivity.
Qed.

(** It is then possible to combine it with the intro pattern for rewriting to
    directly simplify the goal: *)

Goal forall n m, S n = S 0 -> n + m = m.
  intros n m [= ->]. cbn. reflexivity.
Qed.

(** Another way of simplifying an equality is when it is absurd like [S n = 0]
    in which case we can prove the goal automatically using [discriminate].
    This is also possible autimatically thanks to the [=] pattern:
*)

Goal forall n, S n = 0 -> False.
Proof.
  intros n [=].
Qed.



(** ** 5. Applying Lemmas *)


Theorem app_eq_unit {A} (x y:list A) (a:A) :
    x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
Proof.
  destruct x; cbn.
  - intros ->. left. easy.
  - intros [= -> [-> ->]%app_eq_nil]. right. easy.
Qed. 