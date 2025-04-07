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

(*
-> plus
-> once
-> once_plus
-> orelse (||) and ++
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.


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


    (* Reimplement || and + *)

(* Let us code a "++" combinator that given two tactics :
-
-
-

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

(** Because Lta2 is a call-by-value language, we must put tactic into a "thunk"
    before passing to [orelse], otherwise it would be evaluated on the fly,
    and all the work done by [orsele] by pointless.

    In order not to have it to do it ourselves in the code, we define
    the Ltac2 Notation calling the [orelse] to automatically insert "thunk"
    around our tactics.
*)

Ltac2 Notation "or||" tac1(thunk(tactic(6))) tac2(thunk(tactic(6))) :=
  orelse tac1 tac2.

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
  (* Apply the first tactic that succeeds *)
  - orelse (fun _ => exact 2) (fun _ => exact 1).
  - orelse (fun _ => assumption) (fun _ => reflexivity).
  (* Fails if none of the tactic succeeds *)
  - Fail orelse (fun _ => assumption) (fun _ => exact 4).
Abort.

(* However, [orlse] will not backtrack on the choice of the tactic to apply
   in case of the choice causes subsequent failure
*)
Goal exists n, n = 2.
  unshelve econstructor.
  (* It applies [exact 1] as it is the first tactic to succeeds, which leads to
     [1 = 2], it then fails on [reflexivity] rather than backtracking to do [exact 2]. *)
  Fail all: only 1: orelse (fun _ => exact 1) (fun _ => exact 2); reflexivity.



(* Instead of [||], we could prefer the operator [+] that will backtrack on his
   choice of tactic if the tactic later failed.

To do so, we use Control.plus. This is the most direct use of [Control.plus].
It install a backtracking point around [tac1], that is it
1. Execute [tac1] until tac1 produces a value ???
2. If [tac1] fails, it backtracks and execute [tac2]

 *)

Ltac2 or_backtrack (tac1 : unit -> 'a) (tac2 : unit -> 'a) : 'a :=
  Control.plus tac1 (fun _ => tac2 ()).

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
  (* Apply the first tactic that succeeds *)
  - or_backtrack (fun _ => exact 2) (fun _ => exact 1).
  - or_backtrack (fun _ => assumption) (fun _ => reflexivity).
  (* Fails if none of the tactic succeeds *)
  - Fail or_backtrack (fun _ => assumption) (fun _ => exact 4).
Abort.

(* Opposite to [orelse], [or_backtrack] will backtrack on the choice in case of failure.
*)
Goal exists n, n = 2.
  unshelve econstructor.
  (* It applies [exact 1] as it is the first tactic to succeeds, which leads to
     [1 = 2], it then fails on [reflexivity] rather than backtracking to do [exact 2]. *)
  all: only 1: or_backtrack (fun _ => exact 1) (fun _ => exact 2); reflexivity.

(* This is a key difference that one should always keep in mind when handling backtracking.
   In particular, while [or_backtrack] will succeed on more goals, backtracking
   like that can be expensive, particular if the tactics between the backtracking point
   and the failure point are expensive.
*)



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
