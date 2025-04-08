(** * Tutorial Ltac2 : Backtracking

  *** Summary

  Ltac2 has native support for backtracking, and powerful primitives to
  manipulate it enabling us to write powerful automatisation proof script.
  While powerful, backtracking and its primitives can be a bit unsetteling for newcommers.
  In this tutorial, we explain how backtracking works in Ltac2, and
  how to use the different primitives to manipulate bactracking by recoding
  basics tactics that were hardcoded in Ltac1.

  *** Table of content

  - 1. Manipulating Tactics with Ltac2, and Thunks
  - 2. Backtracking in Ltac2
  - 3. Manipulating Backtracking with Ltac2 primitives

  *** Prerequisites

  Needed:
  - Already know the basics of Ltac2, and having used it before.

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

  Disclamer: You can go a **long way** with Ltac2 without ever needing to
    directly manipulate backtracking, outside of backtracking tactics like
    [constructor], [only] and [match!]. This tutorial is for advanced users of
    Ltac2, or for users wanting a deeper understanding of how backtracking
    works.
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






(** ** 2. Backtracking in Ltac2

  (* 2.1 Intuition *)


    BEGIN --- CLARIFY

    Backtracking is primitive to Ltac2.
    This means that every object of the language has by default the possibility to backtrack.

    Formally, what it means is that an object of type ['a] does not represent
    one object ['a] but a stream of objects.
    That is a potentially infinite list of objects of type ['a]

    END --- CLARIFY


  (* TO KEEP ??? *)
    [tac1 ; tac2] is basically evaluates with the following workflow:
    1. [tac1] is evaluated first, either:
      - To a value [t] and the rest of the stream [x].
        In this case it tries to apply [t], and if this fails it
        evaluates recursively the stream [x] until it finds a value
        that succeeds or reaches an error and fail.
      - To an error [e] in which case [tac1 ; tac2] fails with error [e],

    2. If step 1. succeeds, it starts evaluating [tac2], which proceeds like
       evaluation of [tac1] up to managment of errors. Either it evaluates:
       - To a value [t] and the rest of the stream [x].
          In this case it tries to apply [t], and if this fails it
          evaluates recursively the stream [x] until it finds a value
          that succeeds or reaches an error and fail.
       - If it fails on an error, it revert the action of [t],
         and restart the evaluation provess at [x; tac2].


  To understand this flow better, let us consider the tactic
  [constructor; reflexivity] to solve the goal [0 = 1 \/ 1 = 1].

  - 1. [constructor] evaluates to [apply left], which is a tactic that can be applied,
        and a rest of the contination [x],
  - 2. It evaluates [reflexivity] and tries to apply it
  - 3. This fails has [0] is not equal to [1].
  - 4. It reverts the action of [apply left], and start evaluating recursively [x; tac2]
  - 5. [x] evalutes to [apply right], which is a tactic that can be applied,
        and a continuation [y],
  - 6. It evaluates [reflexivity] and tries to apply it, which solves the goal


    Constructor => [apply left | apply right]
      1. Evaluates constructor to [apply left | x]
      2. Apply [apply left] => succeeds
      3. Apply [reflexivity] => fail
      4. Backtracks to [constructor], and evaluates the rest of the stream [x]
         for next value which produces [apply right]
      5.
*)

Goal 0 = 1 \/ 1 = 1.
  constructor; print_goals; reflexivity.
Qed.

(* 2.2 Link with streams *)

(** The intuition that this corresponds to stream can be seen by defining
    stream as a Ltac2 type, and transforming any stream into a value,
    and any term into a stream.
 *)

Ltac2 Type rec 'a backtracking_stream :=
  [ EmptyStream(exn)
  | ConsStream('a, (exn -> 'a backtracking_stream)) ].

(* To go from value to stream, we use the primitive [Control.case] to evaluate
   a thunk value, and check whether it produces an error [e], or a value [v]
   and a continuation [h].
   If it produces an error, we just return the empty strem as there is nothing to evaluate.
   If it produces a value, we just add it to the recursive evaluation of the continutation.
*)

Ltac2 rec to_stream (t : unit -> 'a) : 'a backtracking_stream :=
  match Control.case t with
  | Err e => EmptyStream e
  | Val (v, h) => ConsStream v (fun e => to_stream (fun () => h e))
  end.

(** To go from a stream to a value, we check whether the stream is a Empty or not.
    If it is empty, we return [Control.zero] that represents the non-empty value.
    If it is a constant, we use [Control.plus] to add ? to ?
*)

Ltac2 rec from_stream (s : 'a backtracking_stream) : unit -> 'a := fun () =>
match s with
| EmptyStream e => Control.zero e
| ConsStream hd tl => Control.plus (fun () => hd) (fun e => from_stream (tl e) ())
end.

(* Handling exceptions *)




(*

    Basically, every object ['a] is a stream of possibility

 ** Primitives to Handle Backtracking

There are three simple but very powerful primitives to handle backtracking in Ltac2:

- Control.zero : exn -> 'a
- Control.plus : (unit -> 'a) -> (exn -> 'a) -> 'a
- Control.case : (unit -> 'a) -> ('a * (exn -> 'a)) result



*)



(** ** 3. Manipulating Backtracking with Ltac2 primitives

    *** 3.1 Using Control.Plus

    To understand how [Control.plus] works, let us implement a [or] tactical
    that given two tactics [tac1 or tac2] will:

    1. Execute [tac1] until it produces a success, or run out of possibilities,
       in which case execute [tac2]
    2. If [tac1 ++ tac2] succeeds but the value returned leads to a subsequent
       failure when composed with another tactic, i.e. [tac1 ++ tac2 ; ... ; tac3],
       then it backtracks to [tac1 ++ tac2] to find another success, possibly
       trying [tac2] if they are no possible success left in [tac1].

    This can be coded very simple using the [Control.plus] primitive.
    Given two tactics [tac1 tac2: unit -> unit], [tac1 ++ tac2] consists in
    using [Control.plus] to install a backtracking point around [tac1],
    runnning [tac2] in case of exhaustion and failure of [tac1].

    This does satify the specification as:
    - This will indeed apply the first tactic that work first, as it tries
      [tac1] first, and tries [tac2] onyl if [tac1] fails.
    - This will indeed backtrack in case of subsequent failure and try [tac2] if
      needed, as backtracking is the default behaviour of [;], and we simply
      added [tac2] to additionnaly try if [tac1] fails.

    If this feels confusing, a good practice is to see it from the perspective
    of the stream model. In this particular case, it makes the problem easy.
    Here, we want to try all the possibilities of [tac1], then all the
    possibilities of [tac2] until one succeeds or none are remaining, and it fails.
    In other words, we want to build the concatenation of the stream of [tac1]
    and of the stream of [tac2]. That is exactly what [Control.plus] does.

*)

Ltac2 or_backtrack (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  Control.plus tac1 (fun _ => tac2 ()).

(** Now that we have define [or_backtrack], let us define an infix notation for it.
*)

Ltac2 Notation tac1(thunk(self)) "++" tac2(thunk(self)) :=
  or_backtrack tac1 tac2.

(** Now we have a nice notation to use it, let us tests it to ensure it works.
    That is important because it is easy to make mistakes when dealing with
    backtracking, for instance to forget side cases.
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

(** Moreover, [tac1 ++ tac2] should backtrack to pick the next success,
    possibily trying [tac2], if a choice leads to a subsequent failure.

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
    That is why we talk about successes and not of the result: everything can backtrack.
    For instance, our tactic could be [(tac1 ++ tac2) ++ tac3].
    In this case, it should try all the successes of [ltac1 ++ ltac2], that is
    all the ones of [ltac1] before the one of [ltac2], before trying [tac3].

    We can easily check that our implementation is correct and tries
    the successes in the good order by printing the goals.
 *)

Goal exists n, n = 3.
  unshelve econstructor.
  (* The goals should be [1 = 3], [2 = 3], [3 = 3] *)
  all: only 1: ((exact 1) ++ (exact 2)) ++ (exact 3); print_goals; reflexivity.
Qed.



(** *** 3.2 Using [Control.Case] to control backtracking

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
    For instance, with tactics that make a different choice depending on the
    shape of an hypothesis or of the goal, which are affected in non trivial
    ways by past choices.
    Therefore, it can be difficult to predict which goals will results from
    complex combined backtracking, and hence to scripts that are hard to debug
    when failing.


    We want instead to code a [||] tactical that for [tac1 || tac2] will apply
    the first tactics that succeeds, but will not backtrack if the choice leads
    to subsequent failure.

    To do this, we need to use the [Control.case] to compute [tac1] and to
    check whether it fails or not.

    If it fails, we execute [tac2], and otherwise, we return the first success
    of [tac1] that works using [Control.plus].
*)

Ltac2 orelse (tac1 : unit -> 'a) (tac2 : unit -> 'a) : 'a :=
  match Control.case tac1 with
  | Err _ => tac2 ()
  | Val (x,k) => Control.plus (fun _ => x) k
  end.

Ltac2 Notation tac1(thunk(self)) "||" tac2(thunk(self)) :=
  orelse tac1 tac2.

(** We can now try the previous to tests that this still applies the first
    tactic that succeeds.
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
    (* If the first tactic succeed, it should be picked *)
  - (exact 2) || (exact 1).
    (* If the first tactic failed, the second should be picked *)
  - assumption || reflexivity.
    (* If none works, it should fail returning the last error message *)
  - Fail assumption || (exact 4).
Abort.

(** Moreover, compared to [++], [||] will not backtrack on the choice [tac1] v.s. [tac2].
    However, this does not disable the backtraking abilities of [tac1] and [tac2]
    in case of subsequent failure.
    If [tac1] or [tac2] is picked, it can still backtrack due to subsequent failure.
*)

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [exact 1] and can not backtrack to try [exact 2] *)
  Fail all: only 1: (exact 1) || (exact 2); print_goals; reflexivity.
  (* It picks [(exact 1) ++ (exact 2)] which can backtrack *)
  all: only 1: ((exact 1) ++ (exact 2)) || (exact 3); print_goals; reflexivity.
Abort.

Goal 0 = 2 -> 0 = 2.
Fail all: only 1: (exact 1) || (exact 2); print_goals; reflexivity.
  all: only 1: ((exact 1) ++ (exact 2)) ++ (exact 3); print_goals; reflexivity.
Abort.


(* 3.3 Using [once] to control backtracking *)



(*
Explain the link with
- once
- control_plus

*)





(** *** 3.4. Backtracking and Goal Focusing *)


Goal (True \/ False) /\ (False \/ True).
  Fail split; left ++ right; print_goals; econstructor.









(* ELSE *)

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


