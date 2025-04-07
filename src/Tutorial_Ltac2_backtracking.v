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

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

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
  let us remind how to manipulate tactics with Ltac2 functions.

  Tactics such as [assumption] or [left] modify the proof state through side effects,
  such as modifying hypotheses or resolving an existential variable.
  They do not produces Ltac2 value, like an integer [Int] of Ltac2, and are
  hence of type [unit].

  Opposite to Rocq that is call-by-name, Ltac2 is language that is call-by-value.
  This means that a Ltac2 function evaluates its arguments before evaluating the body of the function.
  Being call-by-value is important for a functional programming language like Ltac2
  to be predicatable and intuitive.

  However, this has an important side effect to manipulate tactics.
  If we pass a tactic like [fail] **as is** to a Ltac2 function,
  it will be evaluated first.

  As [fail] fails, the whole Ltac2 tactic will fail, even if the tactic [fail]
  is not used.
  For instance, consider a function doing ignoring its arguments, and doing nothing.
  Applying it directly to [fail] will fail.
*)

Ltac2 bad_ignore (bad_tac : unit) : unit := ().

Goal 0 = 0.
  Fail bad_ignore fail.
Abort.

(** Consequently, tactics must be "thunk" to be manipulated by a Ltac2 function.
    That is, rather than manipulating [tac : unit] directly, a Ltac2 function
    manipulates it is "thunk" version instead [fun _ => tac : unit -> unit].
    As function are alrady fully-evaluated in call-by-value, "thunk" do
    not get reduced further when passed as arguments of functions, and
    can hence be evaluated on demand [(fun _ => tac) ()] by Ltac2 functions.

    A [good_ignore] function, would hence be of the following type, and we can
    check it works:
*)

Ltac2 good_ignore (tac : unit -> unit) : unit := ().

Goal (0 = 0).
  (* succeeds doing nothing  *)
  good_ignore (fun _ => fail).
Abort.

(** While, this works, no one wants to write "thunk" by hand in proof script.
    Thanfully, there is an easy not to have to. It suffices to define
    a Ltac2 notation that directly inserts the thunk around tactics.
    For instance, for [good_ignore] we declare a notation with the same
    name, that takes a tactic as argument that is "thunk", i.e. [tac(thunk(tactic))].
    It is then possible to write clean proof script as usual, while having a
    meta-programming language with a clear semantics, opposite to Ltac1.
*)

Ltac2 Notation "good_ignore" tac(thunk(tactic)) := good_ignore tac.

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


(* 2.1 A Backtracking or *)

(** To understand how [Control.plus] works, let us first consider how to use it
    to code a [or] tactical that given two tactics [tac1 or tac2] will:
    1. Execute [tac1] until tac1 produces a succes
    2. If [tac1] produces no success, then it execute [tac2]
    3. If [tac1 + tac2] succeeds but the value returned leads to a subsequent failure
       when composed with another tactic, i.e. [tac1 + tac2 ; ... ; tac3],
       then it backtracks to [tac1 + tac2] to find another success,
       possibly in [tac2] if they are none left in [tac1].


Defining an [or] that backtracks is a very direct application of [Control.plus]
Given two tactics [tac1 tac2: unit -> unit], [or_backtrack]

*)



Ltac2 or_backtrack (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
 Control.plus tac1 (fun _ => tac2 ()).


Ltac2 Notation tac1(thunk(self)) "++" tac2(thunk(self)) :=
  or_backtrack tac1 (fun _ => tac2 ()).

Goal exists n, n = 2 /\ n = 3.
 unshelve econstructor; only 2 : split.
 (* Apply the first tactic that succeeds *)
 - (exact 2) ++ (exact 1).
 - assumption ++ reflexivity.
 (* Fails if none of the tactic succeeds *)
 - Fail assumption ++ (exact 4).
Abort.

(* If a choice fails, then it will backtrack to the original choice
*)
Goal exists n, n = 2.
 unshelve econstructor.
 (* The first succes is [exact 1] which leads to the goal [1 = 2].
    This latter leads to a failure as [reflexivity] can not solve the goal [1 = 2].
    The proof script hence backtracks to apply [exact 2] which succeeds, then
    run the proof script again which this time succeeds. *)
 all: only 1: (exact 1) ++ (exact 2); print_goals; reflexivity.
Qed.

Goal exists n, n = 3.
 unshelve econstructor.
 (* The first succes is [exact 1] which leads to the goal [1 = 2].
    This latter leads to a failure as [reflexivity] can not solve the goal [1 = 2].
    The proof script hence backtracks to apply [exact 2] which succeeds, then
    run the proof script again which this time succeeds. *)
 all: only 1: ((exact 1) ++ (exact 2)) ++ (exact 3); print_goals; reflexivity.
Qed.


(** In practice this behaviour is not always wanted as it can make proof scripts
    costly, or hard to predict.
    For instance, suppose we have a script of the form [tac1 ++ tac2; script; tac4]
    with [tac4] failing and causing batracking in [tac1 ++ tac2]:
    - This can be costly as [script] will be repeated for every success
      of [tac1 ++ tac2] until one is found that will make [tac4] succeed.
    - This can cause an exponantial blow up of combinations tried if [script]
      itsel can backtrack.
    - Overall, it can make the proof script unpredicatable as during [script]
      existential variables like [?n] can be resolved differently than expected,
      or lemma applied differently than expected leading to a goal that can
      no longer be solved.

  We want instead to code a [||] tactical that for [tac1 || tac2] will
  apply the first tactic that succeeds, but will not backtrack if the choice
  leads to subsequent failure.

  Comes in play the [Control.case]

To do so we consider

We use [Control.case] to evaluates [tac] and see if returns an error or a value.
1. If [tac] fails with an error [e], we want to try [tac2].
   To do, we pass the error to [tac2] that is free to ignore it or not.
   To check out, what has been attempted, we additionally print the error message
   using [Message.of_exn].
2. If [tac] returns a value [x] and a continuation [k].
   In this case, we want to return the value [x] but preserves the continuation
   to try. To do this, we put the "stream" together with [Control.plus]:

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


