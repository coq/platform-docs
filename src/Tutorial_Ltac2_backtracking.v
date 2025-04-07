(** * Tutorial Ltac2 : Backtracking

  *** Summary
  In Ltac2, every value

  Ltac2 offers powerful primitives to deal with backtracking,
  While powerful this can be a bit unsetteling for newcommers.
  In this tutorial, we introduce them, and explain how to use them
  by recoding basic functionality of Ltac1.


  *** Table of content

  - 1. The concept of backtracking ???
  - 2. Manipulating Backtracking with Ltac2

  *** Prerequisites

  Needed:
  - Already know the basics of Ltac2, and having used it before.

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

  Disclamer:
    You can go a **long way** with Ltac2 without ever needing to directly manipulate backtracking,
    outside of backtracking tactics like [constructor], [only] and [match!].
    This tutorial is for advanced users of Ltac2, or for users wanting a deeper
    understanding of how backtracking works.
*)

(** Let us start by importing Ltac2, and write a small function for
    printing the current goals to check out what is going on.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.

Ltac2 print_goals () :=
  Control.enter ( fun _ =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end
  ).

Ltac2 Notation "print_goals" := print_goals ().

Ltac2 only0 (startgoal : int) (endgoal : int option) (tac : unit -> 'a) : 'a :=
let clamp i :=
  if (Int.lt i 0)
  then Int.add (Int.add i (Control.numgoals ())) 1
  else i
in
let endgoal := Option.default startgoal endgoal in
Control.focus (clamp startgoal) (clamp endgoal) tac.

Ltac2 Notation "only" startgoal(tactic) endgoal(opt(seq("-", tactic))) ":" tac(thunk(tactic)) :=
only0 startgoal endgoal tac.


(** 1. Manipulating Tactics with Ltac2, and Thunks

  Before explaining how to manipualte backtracking with Ltac2,
  let us recall how to manipulate tactics with Ltac2 functions.

  Tactics such as [assumption] or [left] modify the proof state through side effects,
  such as modifying hypotheses or resolving an existential variable.
  They do not produces Ltac2 value, like an integer [Int] of Ltac2, and are
  hence of type [unit].

  Opposite to Rocq that is call-by-name, Ltac2 is language that is call-by-value.
  This means that a Ltac2 function evaluates its arguments before evaluating the body of the function.
  Being call-by-value is important for a functional programming language like Ltac2
  to be predicatable and intuitive.

  However, this has an important side effect to manipulate tactics.
  If we pass a tactic like [fail] **as is** to a Ltac2 function, it will be evaluated first.
  As [fail] fails, the whole Ltac2 tactic will then fail, even if [fail] is not used.
  For instance, consider a function ignoring its arguments, and doing nothing.
  Applying it directly to [fail] will fail, even though it should do nothing.
*)

Ltac2 bad_ignore (bad_tac : unit) : unit := ().

Goal 0 = 0.
  Fail bad_ignore fail.
Abort.

(** Consequently, tactics must be "thunk" to be manipulated by a Ltac2 function.
    That is, rather than manipulating [tac : unit] directly, a Ltac2 function
    manipulates it is "thunk" version instead [fun _ => tac : unit -> unit].
    As function are already fully-evaluated in call-by-value, "thunk" do
    not get reduced further when passed as arguments, and can hence be evaluated
    on demand by Ltac2 functions applying it to [()], [(fun _ => tac) ()].

    A [good_ignore] function would hence have following type, and we can check it works:
*)

Ltac2 good_ignore (tac : unit -> unit) : unit := ().

Goal (0 = 0).
  (* succeeds doing nothing  *)
  good_ignore (fun _ => fail).
Abort.

(** While this works, no one wants to write "thunk" by hand in proof scripts.
    Thanfully, there is an easy not to have to. It suffices to define
    a Ltac2 notation that directly inserts the thunks around tactics for us.
    For instance, for [good_ignore], we declare a notation with the same
    name that takes a tactic as argument that is "thunk", i.e. [tac(thunk(tactic))].
*)

Ltac2 Notation "good_ignore" tac(thunk(tactic)) := good_ignore tac.

(** It is then possible to write clean proof script as usual, while having a
    meta-programming language with a clear semantics, opposite to Ltac1.
*)

Goal 0 = 0.
  good_ignore fail.
Abort.






(** ** 1. Backtracking with Ltac2

    *** 1.1 Working in a Backtracking Monad

    TODOT TEXT
*)

(** ** 1.2 Primitives to Handle Backtracking

There are three simple but very powerful primitives to handle backtracking in Ltac2:

- Control.zero : exn -> 'a
- Control.plus : (unit -> 'a) -> (exn -> 'a) -> 'a
- Control.case : (unit -> 'a) -> ('a * (exn -> 'a)) result



*)



(*
-> plus
-> once
-> once_plus
-> orelse (||) and ++
*)


(** *** 2.1 A Backtracking Or

    To understand how [Control.plus] works, let us first consider how to implement
    a [or] tactical that given two tactics [tac1 or tac2] will:
    1. Execute [tac1] until it produces a success, or run out of possibilities,
       in which case execute [tac2]
    3. If [tac1 + tac2] succeeds but the value returned leads to a subsequent failure
       when composed with another tactic, i.e. [tac1 + tac2 ; ... ; tac3],
       then backtrack to [tac1 + tac2] to find another success,
       possibly in [tac2] if they are none left in [tac1].

Defining an [or] that backtracks is a direct application of [Control.plus].
Given two tactics [tac1 tac2: unit -> unit], [or_backtrack] simply uses [Control.plus]
to install a backtracking point around [tac1], dealing with failure with [tac2] ignoring
the exception that is raised.
*)


Ltac2 or_backtrack (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  Control.plus tac1 (fun _ => tac2 ()).

(** For redability, let us define an infix notation for it:
*)

Ltac2 Notation tac1(thunk(self)) "++" tac2(thunk(self)) :=
  or_backtrack tac1 (fun _ => tac2 ()).

(** We can easily check that the [++] does pick the first tactic to succeed.
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
    (* If the first tactic succeed, it should be picked *)
  - (exact 2) ++ (exact 1).
    (* If the first tactic failed, the second should be picked *)
  - assumption ++ reflexivity.
    (* If none works, it should fail returning the last error message *)
  - Fail assumption ++ (exact 4).
Abort.

(** Moreover, it should backtrack to pick the next success of [tac1 ++ tac2]
    if a choice leads to a subsequent failure.

    To check it consider the example below that require a value [n] such that [n = 2].
    The first success is [exact 1] which leads to the goal [1 = 2].
    This latter leads to a failure as [reflexivity] can not solve the goal [1 = 2].
    The proof script hence backtracks to apply [exact 2] which succeeds, then
    run the proof script again, here [reflexivity] which now succeeds as [2 = 2].
*)

Goal exists n, n = 2.
  unshelve econstructor.
  all: only 1: (exact 1) ++ (exact 2); print_goals; reflexivity.
Qed.

(** Something important to understand about backtracking is that a tactic [tac1]
    can have more than one success, as [tac1] can backtrack itself.
    That is why we talk about successes and not of results: everything can backtrack.
    For instance, we could have [tac1 := tac1 ++ tac2], in which case
    [(tac1 ++ tac2) ++ tac3] should exhaust all the successes of [tac1], before
    considering the ones of [tac2], and finally the ones of [tac3].

    We can easily check that our implementation is correct and tries
    the successes in the good order by printing the goals.
 *)

Goal exists n, n = 3.
 unshelve econstructor.
 (* The goals should be [1 = 3], [2 = 3], [3 = 3] *)
 all: only 1: (exact 1) ++ (exact 2) ++ (exact 3); print_goals; reflexivity.
Qed.


(** *** 2.2 Writing a Or that does not backtrack

  In practice, backtracking on subsequent failure is not always wanted
  as it can make proof scripts costly, and hard to predict.

  For instance, consider a script of the form [tac1 ++ tac2; script].
  [script] will be tried for every success of [tac1 ++ tac2] until one is found
  that will make [script] succeed, or all success have been exhausted.
  Repeating [script] this way can be costly if [script] is a complex tactic.
  Moreover, [script] itself could be backtracking causing an exponantial blow up
  of combinations tried, and potential resulting goals:
*)

Goal exists (n m : nat), n = m.
  unshelve econstructor; only 2 : unshelve econstructor.
  all: only 1 : (exact 0) ++ (exact 1) ++ (exact 2);
       only 1 : (exact 10) ++ (exact 9) ++ (exact 2);
      print_goals ; reflexivity.
Qed.

(** This can easily make proof script hard to predict as a choice of success
    affect which tactic will succeed next.
    For instance, consider proving [nat \/ 2 = 2]. If we choose [left], we want
    to choose next [exact 0], but if we choose [right], we want to choose next
    [reflexivity].
*)

Goal nat + (2 = 2).
  (left ++ right) ; reflexivity ++ (exact 0).
Qed.

(** That can quickly become hard to predict when dealing with non-trivial tactics.
    For instance, when dealing with existential variables that can then be
    unified differently, or pattern-matching that will make a different choice
    depending on the shape of an hypothesis or a goal, which are affected in non
    trivial ways by past choices.
    Therefore, it can be difficult to predict which goals will results from
    complex combined backtracking, and hence to scripts that are hard to debug
    when failing.


    We want instead to code a [||] tactical that for [tac1 || tac2] will apply
    the first tactic that succeeds, but will not backtrack if the choice leads
    to subsequent failure.

    To do this, we need to use the [Control.case]



%%% OLD TEXT

To do so we consider

We use [Control.case] to evaluates [tac] and see if returns an error or a value.
1. If [tac] fails with an error [e], we want to try [tac2]. To do, we pass the
   error to [tac2] that is free to ignore it or not. To check out, what has been
   attempted, we additionally print the error message using [Message.of_exn].
2. If [tac] returns a value [x] and a continuation [k]. In this case, we want to
   return the value [x] but preserves the continuation to try. To do this, we
   put the "stream" together with [Control.plus]:

*)

Ltac2 orelse (tac1 : unit -> 'a) (tac2 : unit -> 'a) : 'a :=
  match Control.case tac1 with
  | Err _ => tac2 ()
  | Val (x,k) => Control.plus (fun _ => x) k
  end.

  Ltac2 Notation tac1(thunk(self)) "||" tac2(thunk(self)) :=
  orelse tac1 tac2.

(** Because Lta2 is a call-by-value language, we must put tactic into a "thunk"
    before passing to [orelse], otherwise it would be evaluated on the fly,
    and all the work done by [orsele] by pointless.

    In order not to have it to do it ourselves in the code, we define
    the Ltac2 Notation calling the [orelse] to automatically insert "thunk"
    around our tactics.
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
  (* Apply the first tactic that succeeds *)
  - (exact 2) || (exact 1).
  - assumption || reflexivity.
  (* Fails if none of the tactic succeeds *)
  - Fail assumption || (exact 4).
Abort.

(* However, [orlse] will not backtrack on the choice of the tactic to apply
   in case of the choice causes subsequent failure
*)
Goal exists n, n = 2.
  unshelve econstructor.
  (* It applies [exact 1] as it is the first tactic to succeeds, which leads to
     [1 = 2], it then fails on [reflexivity] rather than backtracking to do [exact 2]. *)
  Fail all: only 1: (exact 1) || (exact 2); reflexivity.
Abort.






(** 2. Backtracking and Goal Focusing *)


Goal (True \/ False) /\ (False \/ True).
  Fail split; left ++ right; print_goals; econstructor.


    (* Reimplement ; *)

(* While in apparence simple, [plus] and [case] are so powerful that
   when combined with recursion, they enable to reimplement the [;] operator.
   Specifically [tac1 ; tac2] should execute [tac1],
   1. if [tac1] fails it should fail
   2. otherwise it should execute [tac2], and in case of failure backtracks to [tac1]

   This case analysis is typicall of the [case] constructor.
   If [tac1] fails, we kill the continutation using [zero e].
   Otherwise, we execute [tac2] using [Control.plus] to install
   a backtracking point around.
*)

(* Check if that is right ? *)
Ltac2 rec concat (tac1 : unit -> unit) (tac2 : unit -> 'a) : 'a :=
  match Control.case tac1 with
  | Err e => Control.zero e
  | Val ( _ , f ) =>
      Control.plus tac2 (fun e' =>
      concat (fun () => f e') (fun _ => tac2 ()))
  end.

(* Goal  *)
Goal 0 = 0 \/ 1 = 2.
  Fail (concat (fun _ => fail) (fun _ => reflexivity)).
  concat (fun _ => left) (fun _ => reflexivity).
Abort.

(* Tests for backtracking *)
Goal 0 = 1 \/ 0 = 0.
  concat (fun _ => constructor) (fun _ => reflexivity).
Abort.


    (* Reimplement only *)


