(** * How to write a contradiction tactic with Ltac2

  *** Authors
  - Thomas Lamiaux

  *** Summary

  This tutorial explains how to write a contradiction tactic using Ltac2.
  In particular, it showcases how to use match goal, quoting, and
  the Constr and Ind API to check properties on inductive types.

  *** Table of content

  - 1. Introduction
  - 2. Matching the goal for [P] and [~P]
    - 2.1 Choosing [lazy_match!], [match!] or [multi_match!]
    - 2.2 Matching Syntactically or Semantically
    - 2.3 Error message
  - 3. Using Constr.Unsafe and Ind API to Add Syntactic Checks
    - 3.1 Checking for Empty and Singleton Types
    - 3.2 Checking for Empty and Singleton Hypotheses
  - 4. Putting it All Together

  *** Prerequisites

  Disclaimer:

  Needed:
  - Basic knowledge of Ltac2

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

*)

From Ltac2 Require Import Ltac2 Constr Printf.

(** ** 1. Introduction

    According to its specification the [contradiction] can take an argument or not.

    If [contradiction] does not take an argument, then [contradiction]:
    1. First introduces all variables,
    2. Try to prove the goal by checking the hypothesis for:
      - A pair of hypotheses [p : P] and [np :~P], such that any goal can be
        proven by [destruct (np p)]
      - An hypothesis [i : I] such that [I] is an inductive type without any constructor
        like [False], i.e. such that any goal can be proven by [destruct i]
      - An hypothesis [ni : ~I] such that [I] is an inductive type with
        one constructor without arguments, like [True] or [0 = 0].
        In other word, such [I] is provable by [constructor 1].

    If [contradiction] takes an argument [t] then, the type of [t] must either be:
    1. An empty like [False], in which case the goal is proven
    2. Or a negation [~P], in which case:
        - There is a hypothesis [P] in the context, then the goal is proven
        - Otherwise, the goal is replaced by [P]


    In this how-to we will see how to code it using Ltac.

*)





(** ** 2. Matching the goal for [P] and [~P]

    *** 2.1 Choosing [lazy_match!], [match!] or [multi_match!]

    To look up for a pair of hypotheses [P] and [~P], we need to match the goal.
    There are three commands to match the goal that have different behaviour
    regarding backtracking. The first step is to understand which one we want to use.

  - [lazy_match! goal with] is the easiest command to understand and to use.
    [lazy_match!] picks a branch, and sticks to it to even if this leads to a failure.
    It will not backtrack to pick another branch if a choice leads to a failure.
    In practice, it is sufficient for all applications where matching the syntax
    is enough and deterministic.

    For instance, in the example below, it picks the first branch as everything
    match [ |- _], choice that leads to failure. It stick to it and fails.
*)

Goal False.
  Fail lazy_match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.

(** - [match! goal with] picks the first branch that succeeds.
      If it picks a branch, and evaluation of it fails, then it backtracks and
      look for next hypothesis fitting the syntax.
      [match!] is useful as soon as matching the syntax is not enough,
      and we need additional tests to see if we picked the good hypothesis or not.
      In this case, a test can fail, and we hence look for another hypothesis
      with the good syntax.

      In the example below the first branch is picked and fails, it hence
      backtracks to its choice, pick the second branch which this time succeeds.
*)

Goal False.
  match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.

(** - [multi_match! goal with] is more complex and subtle. It basically behaves
      like [match!] except that it will further backtrack if the choice of a
      branch leads to a subsequent failure when linked with another tactic.
      [multi_match!] can be hard to predict and should only be used by people
      that understand what is going on, and for tactics meant to be linked with
      other tactics like [constructor].
      We have no use for it here, as [contradiction] is meant to solve goals.
*)


(** *** 2.2 Matching Syntactically or Semantically *)

(** Whether we choose to use [lazy_match!] or [match!], there are different
    way to match for [P] and [~P]. We can match the syntax directly, or match it
    semantically that is up to some reduction, conversion or unification.


    **** 2.2.1 Matching Syntax

    Matching is by default syntactic. Consequently, if we want to match for [P] and
    [~P] syntactic, we can do so directly by using the pattern [p : ?t, np : ~(?t)].
    This pattern is works, then we can prove [False] out of it.
    Consequently, we can use [lazy_match!] for it.

    Getting [p : ident] and [np : ident], we can not prove the goal directly
    with [destuct (np p)] as [destruct] expects a Rocq term, whereas
    [p] and [np] are identifier, the names of the hypothesis.
    To get the term associated to [p] and [np], we must use [Control.hyp : ident -> contr].
    We must then use [$] to go back to a Rocq term.
*)

Ltac2 match_PnP_syntax () :=
  lazy_match! goal with
  | [p : ?t, np : ~(?t) |- _ ] =>
        printf "Matching succeeded";
        printf "Hypotheses are %I,%I,%t" p np t;
        let p := Control.hyp p in
        let np := Control.hyp np in
        destruct ($np $p)
  | [ |- _ ] => printf "Matching failed"; fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_syntax ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_syntax ().
Abort.

(** It has the advantage to be fast but the downside is that it will not match
    [?t -> False], even though it is convertible to [~(?t)].
    It is not what we want for a [contradiction] tactic.
*)

Goal forall P, P -> (P -> False) -> False.
  intros. Fail match_PnP_syntax ().
Abort.

(** It can not solve evariables either, as it is purely syntactic *)

Goal forall P, P -> False.
  intros. eassert (X4 : _) by admit.
  Fail match_PnP_syntax ().
Abort.

(** To deal with [?t -> False], we could be tempted to add an extra-pattern in
    the definition, but this would not scale. Any variations around [~] would fail.
*)

Goal forall P, P -> ((fun _ => ~P) 0) -> False.
  intros. Fail match_PnP_syntax ().
Abort.

(** Checking terms up to syntax is not a good notion of equality in type theory.
    For instance, [4 + 1] is not syntactically equal to [1]
    What we really want is to compare type semantically, i.e. up to conversion
    or unification.
*)


(** **** 2.2.2 Matching up to Unification

    To match up conversion or unification, we must match for a pair of hypotheses
    [p : ?t1, np : ?t2 |- _], then check that [t2] is of the form [t1 -> False].

    Checking terms up to unification can be done exploiting that tactics
    check terms up to unification.
    [$np $p] is well-typed only if the type of [np], [t2] is of the form [t1 -> X].
    We also need to ensure [X] is [False], otherwise, [destruct ($np $p)] we
    could just pattern matching on [nat], which would not solve the goal.
    We can ensure it does solve the goal by wrapping it in [solve].
    However, it is not an efficient solution, as we would still do [destruct] for
    every pair of hypotheses until we found one that works, which can be costly.
    A better solution, is to use a type annotation [$np $p : False] to force the
    type of [$np $p] to be [False].

    Something fundamental to understand, is that with this approach the syntax
    check is no longer sufficient to be able to prove [False], as we match for
    any pair of hypotheses.
    We hence need to switch from [lazy_match!] to [match!] to be able to
    backtrack and try the next hypotheses, if we have picked the wrong ones.
*)

Ltac2 match_PnP_unification_v1 () :=
  match! goal with
  | [p : ?t1, np : ?t2 |- _ ] =>
        printf "Matching succeeded";
        printf "Hypotheses are %I : %t, and %I : %t" p t1 np t2;
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p : False))
  | [ |- _ ] => fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_unification_v1 ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_unification_v1 ().
Abort.

Goal forall P, P -> (P -> False) -> False.
  intros. match_PnP_unification_v1 ().
Qed.

Goal forall P Q, P -> ~Q -> False.
  intros. eassert (X4 : _) by admit.
  match_PnP_unification_v1 ().
Abort.

(** While this technically works, a better and more principled approach is to
    directly us the primitive [Std.unify : constr -> constr -> unit] that
    that unifies two terms, and raises an exception if it is not possible.

    With this approach, there are much less chances to make an error,
    like misunderstanding how unification is done by the tactics, or
    forgetting the type annotation [: False].

    Moreover, it scales much better. There is currently no conversion primitive
    in Ltac2 (it is comming), but if they were  once, we could basically replace
    [Std.unify] by [Std.conversion] to get the other version.
    Once could even consider parametrising the code by a check that could later
    be instantiated with unification, conversion or some syntax check up to
    reduction, like to head normal form.
*)

Ltac2 match_PnP_unification_v2 () :=
  match! goal with
  | [p : ?t1, np : ?t2 |- _ ] =>
        printf "Matching succeeded";
        printf "Hypotheses are %I : %t, and %I : %t" p t1 np t2;
        Std.unify t2 '($t1 -> False);
        printf "Unification Worked!";
        let p := Control.hyp p in
        let np := Control.hyp np in
        destruct ($np $p)
  | [ |- _ ] => fail
  end.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. match_PnP_unification_v2 ().
Qed.

Goal forall P, P -> (P -> nat) -> False.
  intros. Fail match_PnP_unification_v2 ().
Abort.

Goal forall P, P -> (P -> False) -> False.
  intros. match_PnP_unification_v2 ().
Qed.

Goal forall P Q, P -> ~Q -> False.
  intros. eassert (X4 : _) by admit.
  match_PnP_unification_v2 ().
Abort.

(** We will use this version in this how-to guide.  *)


(** *** 2.3 Error Messages

  So far, we have been returning a [fail] in case of failure, which return
  the error message [Tactic_failure None].

  We can be finer using the primitive [Control.zero : exn -> 'a] to raise an error.
  We can then raise a custom error message using [Tactic_failure : message option -> exn]
  that returns an error for any given message.
  We can then write complex error message using [fprintf] that behaves as [printf]
  excepts that it returns a [message] rather than printing it.
*)

Goal forall P, P -> (P -> nat) -> False.
  Fail match! goal with
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "No such contradiction")))
  end.
Abort.

(** The error type [exn] is an open type, which mean we can a constructor to it,
    i.e. a new exception at any point.
    We can hence create a new exception just for contradiction.
*)

Ltac2 Type exn ::= [ Contradiction_Failed (message option) ].

Goal forall P, P -> (P -> nat) -> False.
  Fail match! goal with
  | [ |- _ ] => Control.zero (Contradiction_Failed (Some (fprintf "No such contradiction")))
  end.
Abort.


(** ** 3. Using Constr.Unsafe and Ind API to Add Syntactic Checks

    We need to check for hypotheses that are either empty like [False], or
    of form [~t] where [t] is an inductive type with one constructor without
    arguments like [nat] or [0 = 0] that we can prove with [constructor 1].

    We can do so very directly by trying to solve the goal assuming we have
    found the good hypotheses wrapping it in [solve] to ensure it works.
    In this case, for [p : t] and [p : ~t] that would mean doing
    [solve [destruct $p]] and [destruct ($np ltac2(constructor 1))].
    However, that would be very inefficient as we would do [destruct] on
    any hypothesis, which and can be expensive.

    A better approach is to add a syntax check that verify that [t] is of the
    appropriate form. It is much cheapar as it is basically matching syntax.
    We can do so by using the API [Constr.Unsafe] that enables to access the
    internal syntax of Rocq terms, and [Ind] to access inductive types.

    The API "unsafe" is named this way because as soon as you start manipulating
    internal syntax, there is no longer any guarantee you create well-scoped terms.
    Here, we will only use it to match the syntax so there is nothing to worry about.
*)


(** *** 3.1 Checking for Empty and Singleton Types

    In both case, the first step is to check the term is an inductive type.
    Internally, a type like [list A] is represented as [App (Ind ind u) args]
    where [ind] is the name of the inductive and the position of the block,
    and [u] represents universe constrains.
    Consequently, given a [t : constr] we need to decompose the application
    [App x args], then match [x] for [Ind ind u].

    This can be done using [Unsafe.kind : constr -> kind] that converts a [constr]
    to a shallow embedding of the internal syntax, which is represented by a Ltac2
    inductive type [kind] that we can then match.
    It is said to be shallowed embedding a [constr] is not fully converted to
    a representation of the internal syntax, only its head.
    For instance, the type of [Unsafe.App] is [constr -> constr array -> kind]
    rather than [kind -> kind constr -> kind].
    The reason is that it is much faster than fully converting terms and
    sufficient for most applications.

   Let us first write a function [decompose_map] that translates a [constr] to
   [kind], then match it for [Unsafe.App]. Notice, we use [match] and not
   [match!] as we are matching a Ltac2 inductive [kind] and not a [constr].
   Note it is available by default with Rocq 9.1 or above.
*)

Import Ind.

Ltac2 decompose_app (t : constr) :=
  match Unsafe.kind t with
    | Unsafe.App f cl => (f, cl)
    | _ => (t,[| |])
  end.

(** Getting the inductive data associated to an inductive block is similar.
    We first use [decompose_app] to recover the left side of the application,
    we then convert to the syntax to check if it is an inductive, in which case
    we recover the inductive definition with [Ind.data : inductive -> data].

    A subtlety to understand is that [Unsafe.kind] converts the syntax without
    reducing terms. So if we want [(fun _ => True) 0] to be considered as an
    inductive, we need to reduce it first to a head normal form with
    [Std.eval_hnf : constr -> constr].
 *)

Ltac2 get_inductive_body (t : constr) : data option :=
  let (x, _) := decompose_app (Std.eval_hnf t) in
  match Unsafe.kind (Std.eval_hnf x) with
  | (Unsafe.Ind ind _) => Some (Ind.data ind)
  | _ => None
  end.

(** We are ready to check if a type is empty or not, which is now fairly easy.
    Given the definition of an inductive type, it suffices to get the number
    of constructor with [nconstructors : data -> int], and check it is zero.
*)

Ltac2 is_empty_inductive (t : constr) : bool :=
 match get_inductive_body t with
 | Some ind_body => Int.equal (Ind.nconstructors ind_body) 0
 | None => false
 end.

(** We can check an inductive type is a singleton similarly, except to one small issue.
    The primitive to access the arguments of a constructor is only available in
    Rocq 9.1 or above. So for now, we will hence only check that it has only one constructor.
    Though this is not perfect and forces us to wrap [destruct ($np ltac2:(constructor 1)]
    in [solve], it still rules out a lot of potential terms like [nat].
*)

Ltac2 is_singleton_type (t : constr) : bool :=
  match get_inductive_body t with
  | Some ind_body => Int.equal (Ind.nconstructors ind_body) 1
  | None => false
  end.


(** *** 3.2 Checking for Empty and Singleton Hypotheses

    Writing a tactic to check for empty hypothesis is very easy.
    We just match the goal using [match!] as the syntax check is not complete,
    then check if it is empty, and if it is, prove the goal with [destruct $p].
*)

Ltac2 match_P_empty () :=
  match! goal with
  | [ p : ?t |- _ ] =>
        if is_empty_inductive t
        then let p := Control.hyp p in destruct $p
        else fail
  | [ |- _ ] => Control.zero (Contradiction_Failed (Some (fprintf "No such contradiction")))
  end.

Goal False -> False.
  intros. match_P_empty ().
Qed.

Goal True -> False.
  intros. Fail match_P_empty ().
Abort.

(** Checking for the negation of an inductive type is a little bit more involved
    as we need to check the type of [?] is of the form [?X -> False].
    We can do by creating a fresh evariable of type [Type] with
    [open_constr:(u :> Type)] then using [Std.unfiy]:
*)

Ltac2 match_nP_singleton () :=
  match! goal with
  | [ np : ?t |- _ ] =>
        let x := open_constr:(_ :> Type) in
        Std.unify t '($x -> False);
        printf "%t was unified with %t" t '($x -> False);
        if is_singleton_type x
        then let np := Control.hyp np in
              solve [destruct ($np ltac2:(constructor 1))]
        else printf "%t is not a singeleton" x ; fail
  | [ |- _ ] => Control.zero (Contradiction_Failed (Some (fprintf "No such contradiction")))
  end.

Goal ~True -> False.
  intros. match_nP_singleton ().
Qed.

Goal ~(0 = 0) -> False.
  intros. match_nP_singleton ().
Qed.

Goal ~(0 = 1) -> False.
  intros. Fail match_nP_singleton ().
Abort.



(** ** 4. Putting it All Together *)

(** It took a few explanations, but in the end the code of
    [contradiction_empty] is rather short using Ltac2.
*)

Ltac2 contradiction_empty () :=
  intros;
  match! goal with
  | [p : ?t1, np : ?t2 |- _ ] =>
        Std.unify t2 '($t1 -> False);
        let p := Control.hyp p in
        let np := Control.hyp np in
        destruct ($np $p)
  | [ p : ?t |- _ ] =>
        if is_empty_inductive t
        then let p := Control.hyp p in
             destruct $p
        else fail
  | [ np : ?t |- _ ] =>
        let x := open_constr:(_ :> Type) in
        Std.unify t '($x -> False);
        if is_singleton_type x
        then let np := Control.hyp np in
              solve [destruct ($np ltac2:(constructor 1))]
        else fail
  | [ |- _ ] => Control.zero (Contradiction_Failed (Some (fprintf "No such contradiction")))
  end.

(** We also need to write a [contraction] when it takes an argument.
    We create an evariable as before with [open_constr:(_ :> Type)],
    and check the type of [t], [type t} is a negation [$x -> False].
    If it is, we look for a hypothesis of type [$x].
    If there is one, we prove the goal, otherwise, we replace the goal with [$x].
*)

Ltac2 contradiction_arg (t : constr) :=
  let x := open_constr:(_ :> Type) in
  Std.unify (type t) '($x -> False);
  match! goal with
  | [p : ?t2 |- _ ] =>
        Std.unify x t2;
        let p := Control.hyp p in
        destruct ($t $p)
  | [ |- _ ] => assert (f : False) > [apply $t | destruct f]
  end.

Goal forall P, P -> ~P -> 0 = 1.
  intros P p np. contradiction_arg 'np.
Qed.

Goal forall P, ~P -> 0 = 1.
  intros P np. contradiction_arg 'np.
Abort.

Goal forall P, P -> 0 = 1.
  intros P p. Fail contradiction_arg 'p.
Abort.

(** Finally, we define a wrapper for it :  *)

Ltac2 contradiction0 (t : constr option) :=
  match t with
  | None => contradiction_empty ()
  | Some x => contradiction_arg x
  end.

(** We can now use it directly, writing the quoting and [Some] constructor by hand *)

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. contradiction0 None.
Qed.

Goal False -> False.
  intros. contradiction0 None.
Qed.

Goal forall P, P -> ~P -> 0 = 1.
  intros P p np. contradiction0 (Some 'np).
Qed.

Goal forall P, ~P -> 0 = 1.
  intros P np. contradiction0 (Some 'np).
Abort.

(** If we want we can further write a notation to do deal with the [option] and
    the quoting for us, but be aware it may complicate parsing.
*)

Ltac2 Notation "contradiction" t(opt(constr)) := contradiction0 t.

Goal forall P Q, P -> ~Q -> ~P -> False.
  intros. contradiction.
Qed.

Goal False -> False.
  intros. contradiction.
Qed.

Goal forall P, P -> ~P -> 0 = 1.
  intros P p np. contradiction np.
Qed.

Goal forall P, ~P -> 0 = 1.
  intros P np. contradiction np.
Abort.