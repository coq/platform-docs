(** * Tutorial Ltac2 : Backtracking

  *** Summary

  Ltac2 has native support for backtracking, and powerful primitives to
  manipulate it enabling us to write powerful automatisation proof script.
  While powerful, backtracking and its primitives can be a bit unsetteling for newcommers.
  In this tutorial, we explain how backtracking works in Ltac2, and
  how to use the different primitives to manipulate bactracking by recoding
  basics tactics that were hardcoded in Ltac1.

  *** Table of content

  - 2. Backtracking in Ltac2
  - 3. Manipulating Backtracking with Ltac2 primitives
    - 3.1 Using [Control.Plus] to stack possibilities
    - 3.2 Using [Control.Case] to inspect backtracking
    - 3.4 Implementing [once] with [Control.case] and [Control.zero]
          for a finer control of backtracking
    - 3.4 Backtracking and Goal focussing
    - 3.5 Reimplementing [;] using [zero],[plus] and [case]

  *** Prerequisites

  Disclamer:
    - You can go a **long way** with Ltac2 without ever needing to directly
      manipulate backtracking, outside of already backtracking tactics like
      [constructor], [once] and [match!].
      This tutorial is for advanced users of Ltac2, or for users wanting a
      deeper understanding of how backtracking works.

  Needed:
  - Already know the basics of Ltac2.
  - Having used Ltac2 before.

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

*)


(** Let us start by importing Ltac2, and write a small function for
    printing the current goals to check out what is going on.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.

Ltac2 print_goals0 () :=
  Control.enter (fun () =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end
  ).

Ltac2 Notation print_goals := print_goals0 ().

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






(** 1. Introducing on Backtracking

    In Ltac2 backtracking is primitive.

    Every value is by default backtracking, in particular value of types [unit]
    w

    The basic example is the tactic [constructor]:
*)

Goal False \/ True.
  constructor; print_goals; exact I.
Qed.




(* In the stream perpective *)


(** 2. [Control.zero]

    Suppose we want to re-implement a tactic like [eassumption] that checks if
    the goals correponds to an hypothesis, possibily unifying evariables.
    Basically, it amounts to matching the goal for an hypothesis [h] that has
    the same type has the goal to prove, and do exact [h].
    If we don't find a suitable assumption, we have to raise an exception.
    `Control.zero` of type [exn -> unit] is the function for the job.
    It will raise the exception given as an argument, and trigger backtracking.

    Here, we raise a generic exception `Tactic_failure` with an optional error
    message of type [message]:
*)

Ltac2 my_eassumption0 () :=
  match! goal with
  | [ h : ?_a |- ?_a ] => let h := Control.hyp h in exact $h
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "No such assumption")))
  end.

Ltac2 Notation my_eassumption := my_eassumption0 ().

Goal (nat -> False -> True \/ False).
  intros ??.
  Fail my_eassumption.
  (* Uncaught Ltac2 exception: Tactic_failure (Some message:(No such assumption)) *)
  right. my_eassumption.
Qed.

(** Moreover, in case of [failure] it should trigger backtracking.
    We can check it works using [constructor].
*)

Goal nat -> False -> True \/ False.
  intros. constructor; print_goals; my_eassumption.
Qed.

(** You may be accotumed to use [fail], for example, if you are a Ltac1 user.
    In Ltac2, [fail] is easy to understand as it is literraly defined as
    [Control.zero (Tactic_failure None)].
    Therefore, [fail] just is just failure raising the error [Tactic Failure]
    without any further error message.
    It is recommended to use [Control.zero] rather than [fail] to give nice
    error messages in case of failure.
*)

Goal nat.
  Fail fail.
Abort.

(** There is another primitive to raise exceptions [Control.throw : exn -> unit].
    The key difference with [zero] is that [throw] raises a non-catachable exception.
    It means that [throw] will not trigger backtracking.
    It will stop the computation all together.
*)

Goal nat -> False -> True \/ False.
  intros.
  (* This will not backtrack and try to prove [False] *)
  Fail constructor; print_goals; Control.throw (Tactic_failure None).
Abort.

(** Consequently, [throw] should only be used if one **really* wants to prevent backtracking. *)



(** ** 3. [Control.plus] to Catch Exceptions

    Since [Ltac2] has proper exceptions and backtracking is primitive, it is not
    only possible to catch exceptions, but also to backtrack upon them.

    The catching primitive is [Control.plus] of type [(unit -> 'a) -> (exn -> 'a) -> 'a].
    [Control.plus f k] installs a backtracking point around [f]:
    1. it tries all the success of [f], and if there are none, it tries [k]
    2. in case of subsequent failure, it backtracks to [f], and if all its
       sucesses have been exhausted, it tries the continuation [k] for next success.

    To understand [Control.plus], it can be useful to see it from the perspective of the stream model.
    Viewing [f] and [k] as stream of success -- ignoring exceptions for simplicity --
    then [Control.plus f k] is the contatenation of the two streams.
    Indeed, it applies the first success that works, so first checking [f] for one, then [k].
    I case of backtraking, it just try the next succees in the strem, so once again,
    what is left to try in [f], then [k].


    To understand how [Control.plus] works in practice, let us define a or for
    tactics [tac1 ++ tac2], that should:
    1. Apply the first success of [tac1], and if there are none, try [tac2]
    2. In case of subsequent failure, backtrack to [tac1], and if all succeses
       of [tac1] are exhausted, try [tac2]

    This is a direct application of [Control.plus], as it consist in installing
    a backtraking point around [tac1], running [tac2 ()] in case of failure
    of [tac1] disregarding any exception returned by [tac1].
*)

Ltac2 or_backtrack (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  Control.plus tac1 (fun _ => tac2 ()).

(* note, we need to specify thunk by hand with general notations *)
Ltac2 Notation tac1(thunk(self)) "++" tac2(thunk(self)) :=
  or_backtrack tac1 tac2.

(** Now that we have defined [++], let us tests it to ensure it works.
    That is important because it is easy to make mistakes when dealing with
    meta-programming, for instance to forget side cases.
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
    (* If the first tactic succeed, it should be picked *)
  - (exact 2) ++ (exact 1).
    (* If the first tactic failed, the second should be picked *)
  - assumption ++ reflexivity.
    (* If none works, it should return the last error message *)
  - Fail assumption ++ (exact 4).
Abort.

(** In case of subsequent failure, it should bactrack to [tac1] until it has
    exhausted all its success, in which case it should try [tac2]:
 *)

Goal exists n, n = 3.
  unshelve econstructor.
  (* The goals should be [1 = 3], [2 = 3], [3 = 3] *)
  all: only 1: ((exact 1) ++ (exact 2)) ++ (exact 3); print_goals; reflexivity.
Qed.




(** ** 4. Using [Control.Case] to inspect backtracking



  *** 4.1 Reimplement [orelse]

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
    affect which tactics can succeed next, and hence which will be picked next.
    For instance, consider proving [nat \/ 2 = 2].
    If we choose [left], we want to choose [exact 0] next, but if we choose [right],
    we want to choose [reflexivity] next.
*)

Goal nat + (2 = 2).
  (left ++ right) ; reflexivity ++ (exact 0).
Qed.

(** Consequently, we would like a variant of the [++] tactical that
    applies the first tactics that succeeds, but will not backtrack to try
    [tac2] if it has chosen [tac1] and that lead to a subsequent failure.

    To do this, we use [Control.case] to compute [tac1] and check if it fails or not:
    - If it fails, we compute [tac2].
    - If it succeds, we return [tac1] which we have to reconstruct with
      [Control.plus] as we have destructed it with [Control.Case].
*)

Ltac2 orelse (tac1 : unit -> 'a) (tac2 : unit -> 'a) : 'a :=
  match Control.case tac1 with
  | Err _ => tac2 ()
  | Val (x,k) => Control.plus (fun () => x) k
  end.

(*
    This satifies the specification as:
    - It applies [tac1] and if it fails [tac2]
    - This does not backtrack from [tac1] to [tac2] as in case of subsequent failure
      it backtracks to [Control.plus (fun () => x) k] i.e. [tac1].

    In terms of streams, this corresponds to using the stream [tac1]
    if at has at least one success, and the stream [tac2] otheriwse.
    This case analysis naturally corresponds to [Control.Case tac1].
    However, as [Control.case] returns a [result] and not directly a stream,
    we need to use [Control.plus] to glue the result back into [tac1].
*)


(** Now that we have define [orelse], let us define an infix notation for it.
*)

Ltac2 Notation tac1(thunk(self)) "||" tac2(thunk(self)) :=
  orelse tac1 tac2.

(** We can now try the previous to tests that this still applies the first
    tactic that succeeds, but will not backtrack to [tac2] if [tac1] fails:
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

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [exact 1] and can not backtrack to try [exact 2] *)
  Fail all: only 1: (exact 1) || (exact 2); print_goals; reflexivity.

Abort.

(** Note that this does not disable the backtraking abilities of [tac1] and [tac2]:
    if [tac1] or [tac2] is picked, it can still backtrack in case of subsequent failure.
    It only prevents backtracking to try [tac2] if [tac1] was picked.

    This is because, in each branch of [Control.case], we apply [tac1] or [tac2]
    without any further modification, hence preserving their backtracking abilities.
*)

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [(exact 1) ++ (exact 2)] then [excat 1] then backtrack to [exact 2] *)
  all: only 1: ((exact 1) ++ (exact 2)) || (exact 3); print_goals; reflexivity.
Abort.



(** *** 4.2 Reimplement [once]

    Backtracking is allowed by default. To offer better control over it Rocq
    comes with a primtive [once tac] that prevents [tac] to backtrack in case
    of subsequent failure.

    This enables us to have a fine grain control, for instance, in the example before
    we can add it around [(exact 1) ++ (exact 2)] to prevent backtracking.
*)

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [(exact 1) ++ (exact 2)] can not backtrack further due to [once]
     hence backtrack to try [exact 3] *)
  Fail all: only 1: (once ((exact 1) ++ (exact 2))) ++ (exact 3); print_goals; reflexivity.
Abort.

Goal (0 = 0).
  once (assumption ++ reflexivity).
Abort.

(** [once] can be coded easily with [Control.case] and [Control.zero].
    We inspect [tac] to check if it fails or produces a success.
    - If it fails, we return the empty stream.
    - If it produces a success, we return the success, discarding the rest of
      the stream to prevent any backtracking.
*)

Ltac2 my_once0 (tac : unit -> 'a) : 'a :=
  match Control.case tac with
  | Err e => Control.zero e
  | Val(x,_) => x
  end.

Ltac2 Notation my_once := my_once0.

(** A common source of confusion using [Control.case], it to think that this
    will only try the first tactics in the stream of possibilities.
    This is not the case, as [Control.case] return the first success, that is,
    here, the first tactic to work if any.

    For instance, if we try to solve [0 = 0] with [assumption ++ reflexivity]
    the first tactic to succeed is not [assumption] but [reflexivity], which
    will hence be picked by [Control.case (assumption ++ reflexivity)]:
*)

Goal (0 = 0).
  my_once (assumption ++ reflexivity).
Abort.

(** A logical question in now what does the Ltac2 function [once_plus] do?
    It can seem weird at first to add a continuation to try in case of failure
    to use [once] and disable backtracking.
*)

Ltac2 once_plus (run : unit -> 'a) (handle : exn -> 'a) : 'a :=
  once (Control.plus run handle).

(** Well, as [Control.plus] corresponds to [++], this exactly to what was just exlained.
    This does not add potential successes to backtrack to in case of subsequent failure,
    it adds more potential successes to try if [run] produces none.

    Simialry is [once (tac1 ++ tac2)] the same as [tac1 || tac2] ?
    It is not the case. The reason is that [once] prevents backtracking all together.
    Wheras, [tac1 || tac2] only prevents backtracking to try [tac2], if [tac1]
    succeded first. It does not prevent to backtrack to try [tac1] again.
    [once (tac1 ++ tac2)] corresponds to [once tac1 || once tac2].
*)

Goal exists n, n = 2.
  unshelve econstructor.
  (* this fails as no backtracking is allowed *)
  Fail all: only 1: once (((exact 1) ++ (exact 2)) ++ (exact 3)); print_goals; reflexivity.
  (* but this succeds *)
  all: only 1: ((exact 1) ++ (exact 2)) || (exact 3); print_goals; reflexivity.
Abort.





(** *** 3.4 Backtracking and Goal Focusing

  In all previous sections, we have used our tactics with exactly one goal focused.
  What happens if more than one goal is focused ? Does [tac1 ++ tac2]:
  1. must choose [tac1] or [tac2], and apply it to all the goals
  2. it can apply [tac1] or [tac2] independently for each goal

  With the current implementation it must choose [tac1] or [tac2] and apply it everywhere.
  For instance, the following example fails, even though it clearly works if
  the tactic was evaluated independently for every goal.
*)

Goal (0 = 0 \/ 0 = 1) /\ (1 = 0 \/ 1 = 1).
  split.
  Fail all: left ++ right; print_goals; reflexivity.
Abort.

(** The reasons is that it tries to figure one computation path that will succed
    for all the goals.
    In particular, a failure in one goal will trigger backtracking to the first
    goal and try the next success of the tactic for this goal and all the goals,
    this until it has found a success that work in for goals, or exhaust all possibilities.

    This can be seen by trying to prove [(0 = 0 \/ 1 = 1) /\ (1 = 0 \/ 1 = 1)].
    Both [0 = 0] and [1 = 1] are provable, but if we pick [left] to solve the
    first goal, and hence the second goal, we get stuck with [1 = 0] which is not
    provable. It should hence backtrack to pick [right].
*)

Goal (0 = 0 \/ 0 = 0) /\ (1 = 0 \/ 1 = 1).
  split. all: left ++ right; print_goals; reflexivity.
Qed.

(** If you want to apply a tactic independently to every goal, it must be wrapped in
    [Control.enter : (unit -> unit) -> unit], it now works as expected.
 *)

Ltac2 or_backtrack_indep (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  Control.enter (fun () => Control.plus tac1 (fun _ => tac2 ())).

Ltac2 Notation tac1(thunk(self)) "++i" tac2(thunk(self)) :=
  or_backtrack_indep tac1 tac2.

Goal (0 = 0 \/ 0 = 1) /\ (1 = 0 \/ 1 = 1).
  split. all: left ++i right; print_goals; reflexivity.
Abort.




(** *** 3.5 Reimplementing [;] using [zero],[plus] and [case]

    As it turns out, [zero], [plus] [case] are so powerful that when combined
    with recursion they enable us to reimplement the [;] operator.

   Specifically [tac1 ; tac2] should execute [tac1]:
   1. If [tac1] fails it should fail
   2. Otherwise it should execute [tac2], and in case of failure backtracks to [tac1]

  This naturally leads to use [Control.Case] to inspect if [tac1] fails or not.
  - If it fails, we return [Control.zero], rather than [Control.throw], in order
    to fail without breaking previous backtracking points.
  - If [tac1] succeds and return a value [x] and an handler [h],
    we want to execute [tac2] and if it fails backtrack to execute [h ; tac2]
    This corresponds to the [Control.plus] primitive, with recursively calling [concat].

    Note, that here, we do not care about [x] as it has already been evaluated,
    and its side effect, so the tactic already be executed.
*)

Ltac2 rec concat (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  match Control.case tac1 with
  | Err e => Control.zero e
  | Val ( _ , f ) =>
      Control.plus tac2 (fun e' =>
      concat (fun () => f e') (fun () => tac2 ()))
  end.

Ltac2 Notation tac1(thunk(self)) "##" tac2(thunk(self)) :=
  concat tac1 tac2.

(** Let us now check that it work *)

Goal 0 = 0 \/ 1 = 2.
  (* [##] fails if [tac1] fails *)
  Fail (fail ## reflexivity).
  (* it does chain tactics *)
  left ## reflexivity.
Abort.


Goal 0 = 1 \/ 0 = 0.
  (* [##] does backtrack *)
  constructor ## reflexivity.
Abort.