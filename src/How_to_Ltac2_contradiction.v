(** * How to write a tactic Contradiction with Ltac2

  *** Authors
  - Thomas Lamiaux

  *** Summary

  This tutorial explains how to write a contradiction tactic using Ltac2.
  In particular, it showcase how to use quoting, and match goal with
  the Constr API to check properties on terms.

  *** Table of content

  - 1. Introduction
  - 2. Matching the goal for [P] and [~P]
    - 2.1 Choosing [lazy_match!], [match!] or [multi_match!]
    - 2.2 Matching up to syntax, conversion, or unification
    - 2.3 Error message
  - 3. Use the Unsafe API to check for empty and singleton types
    - 2.1 Checking for empty types
    - 2.2 Checking for singleton types
  - 4. Putting it together

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
      - An hypothesis [i : I] such that [I] is an inductive type without any constructor
        like [False], i.e. such that any goal can be proven by [destruct i]
      - An hypothesis [ni : ~I] such that [I] is an inductive type with
        one constructor without hypotheses, like [True] or [0 = 0].
        In other word, such [I] is provable by [constructor 1].
      - A pair of hypotheses [p : P] and [np :~P], such that any goal can be
        proven by [exact (False_rect _ (np p))]

    If [contradiction] takes an argument [t] then, the type of [t] must either be:
    1. An empty like [False], in which case the goal is proven
    2. Or a negation [~P], in which case:
        - There is an hypotheis [P] in the context, then the goal is proven
        - Othewise, the goal is replace by [P]
    *)





(** ** 2. Matching the goal for [P] and [~P]

    *** 2.1 Choosing [lazy_match!], [match!] or [multi_match!]

    To look up for a pair of hypotheses [P] and [~P], we need to match the goal.
    There are three commands to match the goal that have different behaviour
    regarding backtracking. The first step is to understand which one we want to use.

  - [lazy_match! goal with] is the easiest command to understand and to use.
    [lazy_match!] picks a branch, and stick to even if this lead to a failure.
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

      In the example bellow the first branch is picked and fails,
      it hence backtrack to its choice, pick the second which this time succeeds.
*)

Goal False.
  match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.

(** - [multi_match! goal with] is more complex and subtile. It basically behaves
      like [match!] except that it will further backtrack if the choice of a
      branch leads to a subsequent failure when linked with another tactic.
      [multi_match!] can be hard to predict and should only be used by people
      that understand what is going on, and for tactics meant be linked with
      other tactics like [constructor].
      We have no use for it here, as [contradiction] is meant to solve goals.
*)


(** *** 2.2 Matching Syntactically or Semantically *)

(** Whichever we chose to use, there are different way to match for [P] and [~P].
    We can match the syntax directly, or match it semantically that is up to
    conversion or unification.


    TODO: FIX
    All this choices are valid and leads to a different behaviour.
    - Matching syntax has the advantage to be fast, but may not be expressive enough
    - Conversion fully reduces the term and is resonnably fast
    - Unification is the most powerful and expressive as it can solve evariables,
      trigger type class inference etc...



    **** 2.2.1 Matching Syntax

    Matching is by default syntactic. Consequently, if we want to match for [P] and
    [~P] syntactic, we can do so directly by using the pattern [p : ?t, np : ~(?t)].
    This pattern is works, then we we can prove [False] out of it.
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

(** The downside is that it will not match [?t -> False], even though it is
    convertible to [~(?t)]. It is not what we want.
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


(** **** 2.2.2 Matching up to unification

    To match up conversion or unification, we must match for a pair of hypotheses
    [p : ?t1, np : ?t2 |- _], then check that [t2] is of the form [t1 -> False].

    Checking terms up to unification can be done very directly exploiting that
    Rocq term are check up to unification.
    [$np $p] is well-typed only if the type of [np], [t2] is of the form [t1 -> X].
    We also need to ensure [X] is [False], otherwise, [destruct ($np $p)] we
    could just pattern matching on [nat], which would not solve the goal.
    We can ensure it does solve the goal by wraping it in [solve].
    However, it is not an efficient solution, as we would still do [destruct] for
    every pair of hypotheses until we found one that works, which can be costly.
    A better solution, is to use a type annotation [$np $p : False] to force the
    type of [$np $p] to be [False].

    Something fundamental to understand, is that with this approach the syntax
    check is no longer sufficient to be able to prove [False], as we match for
    any pair of hypotheses.
    We hence need to switch from [lazy_match!] to [match!] to be able to
    backtrack and try the next hypotheses, if we have picked the wrongones.
*)

Ltac2 match_PnP_unification_v1 () :=
  match! goal with
  | [p : ?t1, np : ?t2 |- _ ] =>
        printf "Matching succeeded";
        printf "Hypotheses are %I : %t, and %I : %t" p t1 np t2;
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p : False))
  | [ |- _ ] => printf "Matching failed"; fail
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

(** While this technically works, a better and more principaled approach is to
    directly us the primitive [Std.unify : constr -> constr -> unit] that
    that unifies two terms, and raises an exception if it is not possible.

    With this approach there are much less chances to make an error,
    like misunderstanding how unification is done by the tactics, or
    forgetting the type annotation [: False].

    Moreover, it scales much better. There is currently no conversion primitive
    in Ltac2 (it is comming), but if they were we could basically replace
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
  | [ |- _ ] => (printf "the terms are not equal"; fail)
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

(** *** 2.3 Error Messages  *)

(* TODO  *)


(** ** 2. Using Constr.Unsafe to add syntactic check  *)


(*
- need for the test
- intro to unsafe
- empty
- singleton


*)

Import Unsafe Ind.

Ltac2 decompose_app (c : constr) :=
  match Unsafe.kind c with
    | Unsafe.App f cl => (f, cl)
    | _ => (c,[| |])
  end.

  (* empty types *)
Ltac2 is_empty_inductive (t : constr) : bool :=
  let (i, _) := decompose_app (Std.eval_hnf t) in
  match Unsafe.kind (Std.eval_hnf i) with
  | (Unsafe.Ind x _) => Int.equal (Ind.nconstructors (Ind.data x)) 0
  | _ => false
  end.

Ltac2 match_P_empty () :=
  match! goal with
  | [ p : ?t |- _ ] =>
        if is_empty_inductive (Std.eval_hnf t)
        then let p := Control.hyp p in
             destruct $p
        else fail
  | [ |- _ ] => fail
  end.

Goal False -> False.
  intros. match_P_empty ().
Qed.

Goal True -> False.
  intros. Fail match_P_empty ().
Abort.


(** For the moment, we are lacking a primitive to check the number of arguments
    of a constructor, but we can already check that it has only one constructor.
*)
Ltac2 decompose_prod (c : constr) :=
  match Unsafe.kind c with
    | Unsafe.Prod b c => (Binder.type b, c)
    | _ => Control.throw (Tactic_failure None)
  end.

Ltac2 is_singleton_type (t : constr) : bool :=
  let (i, _) := decompose_app (Std.eval_hnf t) in
  match Unsafe.kind (Std.eval_hnf i) with
  | (Unsafe.Ind ind _) =>
        let def_ind := Ind.data ind in
        (Int.equal (Ind.nconstructors def_ind) 1)
  | _ => false
  end.

Ltac2 match_nP_singleton () :=
  match! goal with
  | [ np : ?t |- _ ] =>
        match! (Std.eval_hnf t) with
        | ?x -> ?b =>
            printf "Arrow type";
            Std.unify b 'False;
            printf "Unified to False";
            if is_singleton_type x
            then let np := Control.hyp np in
                 solve [destruct ($np ltac2:(constructor 1))]
            else fail
        | _ => fail
        end
  | [ |- _ ] => fail
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


(** *** 3. Putting it all together *)

(** It took a few explanations, but in the end the code of [contradiction_empty] is
    rather short using Ltac2.
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
        match! (Std.eval_hnf t) with
        | ?x -> ?b =>
            printf "Arrow type";
            Std.unify b 'False;
            printf "Unified to False";
            if is_singleton_type x
            then let np := Control.hyp np in
                 solve [destruct ($np ltac2:(constructor 1))]
            else fail
        | _ => fail
        end
  | [ |- _ ] => (printf "the terms are not equal"; fail)
  end.

(** We also need to do contraction when it takes an argument *)

Ltac2 contradiction_arg (t : constr) :=
  match! Std.eval_hnf (type t) with
  | ?x -> ?b =>
      Std.unify b 'False ;
      match! goal with
      | [p : ?t2 |- _ ] =>
            Std.unify x t2;
            let p := Control.hyp p in
            destruct ($t $p)
      | [ |- _ ] => assert (f : False) > [apply $t | destruct f]
      end
  | _ => Control.zero (Tactic_failure (Some (fprintf "%t : %t is not a negation" t (type t))))
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

(** Finally, we can define a wrapper for it :  *)

Ltac2 contradiction0 (t : constr option) :=
  match t with
  | None => contradiction_empty ()
  | Some x => contradiction_arg x
  end.

(** We can use it directly, writing the quoting and [Some] constructor by hand *)

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

(** If we want we can further write a notation to do deal witht the option and
    the quoting for us, but be aware it can complicate parsing as it reserves a name.
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